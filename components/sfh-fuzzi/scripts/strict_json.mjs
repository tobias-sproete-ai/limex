export function strictJsonParse(text) {
  let index = 0;
  const length = text.length;
  const ws = () => { while (index < length && /\s/.test(text[index])) index += 1; };

  function stringToken() {
    if (text[index] !== '"') throw new Error(`JSON_STRING_EXPECTED_AT_${index}`);
    const start = index++;
    while (index < length) {
      const char = text[index++];
      if (char === '"') return JSON.parse(text.slice(start, index));
      if (char === "\\") {
        if (index >= length) throw new Error("JSON_ESCAPE_TRUNCATED");
        const escaped = text[index++];
        if (escaped === "u") {
          const hex = text.slice(index, index + 4);
          if (!/^[a-fA-F0-9]{4}$/.test(hex)) throw new Error(`JSON_UNICODE_ESCAPE_INVALID_AT_${index}`);
          index += 4;
        } else if (!'"\\/bfnrt'.includes(escaped)) {
          throw new Error(`JSON_ESCAPE_INVALID_AT_${index - 1}`);
        }
      } else if (char.charCodeAt(0) < 0x20) {
        throw new Error(`JSON_CONTROL_CHARACTER_AT_${index - 1}`);
      }
    }
    throw new Error("JSON_STRING_UNTERMINATED");
  }

  function value() {
    ws();
    if (text[index] === "{") return object();
    if (text[index] === "[") return array();
    if (text[index] === '"') { stringToken(); return; }
    const start = index;
    while (index < length && !/[\s,\]}]/.test(text[index])) index += 1;
    if (start === index) throw new Error(`JSON_VALUE_EXPECTED_AT_${index}`);
    JSON.parse(text.slice(start, index));
  }

  function object() {
    index += 1;
    const keys = new Set();
    ws();
    if (text[index] === "}") { index += 1; return; }
    while (index < length) {
      ws();
      const key = stringToken();
      if (keys.has(key)) throw new Error(`JSON_DUPLICATE_KEY:${key}`);
      keys.add(key);
      ws();
      if (text[index++] !== ":") throw new Error(`JSON_COLON_EXPECTED_AT_${index - 1}`);
      value();
      ws();
      const delimiter = text[index++];
      if (delimiter === "}") return;
      if (delimiter !== ",") throw new Error(`JSON_OBJECT_DELIMITER_EXPECTED_AT_${index - 1}`);
    }
    throw new Error("JSON_OBJECT_UNTERMINATED");
  }

  function array() {
    index += 1;
    ws();
    if (text[index] === "]") { index += 1; return; }
    while (index < length) {
      value();
      ws();
      const delimiter = text[index++];
      if (delimiter === "]") return;
      if (delimiter !== ",") throw new Error(`JSON_ARRAY_DELIMITER_EXPECTED_AT_${index - 1}`);
    }
    throw new Error("JSON_ARRAY_UNTERMINATED");
  }

  value();
  ws();
  if (index !== length) throw new Error(`JSON_TRAILING_CONTENT_AT_${index}`);
  return JSON.parse(text);
}
