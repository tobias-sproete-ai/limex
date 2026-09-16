import GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777

/-!
# V1.8.778: unsigned-prefix-summary method-class no-go theorem

V1.8.777 reduces the literal q=3 Abel loss to a real signed correlation.
This module now closes one admissible Quest target: a formal barrier for the
method class that is allowed to inspect only unsigned prefix magnitudes and
the terminal sum of the correlated source.

Two explicit two-point sources have exactly the same complete unsigned
prefix summary and the same terminal sum, but their correlations against the
same fixed signed weight are `2` and `-2`.  Hence no predicate that factors
only through that summary can decide positivity of every admissible signed
correlation.

The theorem is deliberately narrow.  It does not say that the actual
von-Mangoldt source has either sign, and it does not rule out a stronger
carrier-specific theorem using signed residue information.  It proves a
formal no-go result for one precisely defined information class.  Goldbach
itself remains `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodActualQ3UnsignedPrefixSummaryMethodClassNoGoV18778

open GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772

/-- Complete information exposed by a two-point unsigned-prefix method:
the magnitudes of the first and terminal prefixes, together with the signed
terminal sum. -/
def twoPointUnsignedPrefixSummary (x : Fin 2 → Real) : Real × Real × Real :=
  (|x 0|, |x 0 + x 1|, x 0 + x 1)

/-- A predicate is complete for positive signed correlation if it decides
positivity correctly for every two-point source from that source's unsigned
prefix summary alone. -/
def UnsignedPrefixSummaryPositiveComplete
    (decidePositive : (Real × Real × Real) → Prop) : Prop :=
  ∀ x : Fin 2 → Real,
    decidePositive (twoPointUnsignedPrefixSummary x) ↔
      0 < twoPointSignedCorrelation structuralWeight x

theorem structural_sources_same_unsigned_prefix_summary :
    twoPointUnsignedPrefixSummary structuralPositiveSource =
      twoPointUnsignedPrefixSummary structuralNegativeSource := by
  norm_num [twoPointUnsignedPrefixSummary, structuralPositiveSource,
    structuralNegativeSource]

theorem structural_sources_have_opposite_correlation_signs :
    0 < twoPointSignedCorrelation structuralWeight structuralPositiveSource ∧
      twoPointSignedCorrelation structuralWeight structuralNegativeSource < 0 := by
  rw [structuralPositiveSource_correlation,
    structuralNegativeSource_correlation]
  norm_num

/-- Formal method-class barrier: no decision rule that sees only the complete
unsigned prefix summary and terminal sum can correctly decide positivity of
all signed correlations, even on the two explicit admissible sources from
V1.8.772. -/
theorem no_unsigned_prefix_summary_positive_complete_decider :
    ¬ ∃ decidePositive : (Real × Real × Real) → Prop,
        UnsignedPrefixSummaryPositiveComplete decidePositive := by
  rintro ⟨decidePositive, hcomplete⟩
  have hpos :
      decidePositive
        (twoPointUnsignedPrefixSummary structuralPositiveSource) :=
    (hcomplete structuralPositiveSource).2
      structural_sources_have_opposite_correlation_signs.1
  have hnegSummary :
      decidePositive
        (twoPointUnsignedPrefixSummary structuralNegativeSource) := by
    rw [← structural_sources_same_unsigned_prefix_summary]
    exact hpos
  have hnegPositive :
      0 < twoPointSignedCorrelation structuralWeight structuralNegativeSource :=
    (hcomplete structuralNegativeSource).1 hnegSummary
  linarith [structural_sources_have_opposite_correlation_signs.2]

/-- The same obstruction remains after explicitly restricting the domain to
the common prefix-ceiling and zero-terminal class used in V1.8.772. -/
def UnsignedPrefixSummaryPositiveCompleteOnAdmissible
    (decidePositive : (Real × Real × Real) → Prop) : Prop :=
  ∀ x : Fin 2 → Real, TwoPointPrefixAdmissible x →
    (decidePositive (twoPointUnsignedPrefixSummary x) ↔
      0 < twoPointSignedCorrelation structuralWeight x)

theorem no_unsigned_prefix_summary_positive_complete_decider_on_admissible :
    ¬ ∃ decidePositive : (Real × Real × Real) → Prop,
        UnsignedPrefixSummaryPositiveCompleteOnAdmissible decidePositive := by
  rintro ⟨decidePositive, hcomplete⟩
  have hpos :
      decidePositive
        (twoPointUnsignedPrefixSummary structuralPositiveSource) :=
    (hcomplete structuralPositiveSource
      structuralPositiveSource_prefixAdmissible).2
        structural_sources_have_opposite_correlation_signs.1
  have hnegSummary :
      decidePositive
        (twoPointUnsignedPrefixSummary structuralNegativeSource) := by
    rw [← structural_sources_same_unsigned_prefix_summary]
    exact hpos
  have hnegPositive :
      0 < twoPointSignedCorrelation structuralWeight structuralNegativeSource :=
    (hcomplete structuralNegativeSource
      structuralNegativeSource_prefixAdmissible).1 hnegSummary
  linarith [structural_sources_have_opposite_correlation_signs.2]

end GoldbachCircleMethodActualQ3UnsignedPrefixSummaryMethodClassNoGoV18778
