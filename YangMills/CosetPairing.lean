import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace YangMills.DualBook

theorem coset_pairing_doubled
    {V : Type*} [Fintype V] [AddCommGroup V]
    (T : V) (_hT2 : T + T = 0)
    (χ f : V → ℝ) (hχ : ∀ S : V, χ (S + T) = -χ S) :
    2 * (∑ S : V, χ S * f S) = ∑ S : V, χ S * (f S - f (S + T)) := by
  have hshift : ∑ S : V, χ S * f S = ∑ S : V, χ (S + T) * f (S + T) :=
    (Fintype.sum_equiv (Equiv.addRight T) _ _ (fun _ => rfl)).symm
  calc 2 * (∑ S : V, χ S * f S)
      = (∑ S : V, χ S * f S) + (∑ S : V, χ S * f S) := by ring
    _ = (∑ S : V, χ S * f S) + (∑ S : V, χ (S + T) * f (S + T)) := by rw [← hshift]
    _ = ∑ S : V, (χ S * f S + χ (S + T) * f (S + T)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ S : V, χ S * (f S - f (S + T)) := by
        refine Finset.sum_congr rfl (fun S _ => ?_); rw [hχ S]; ring

theorem coset_pairing_transversal
    {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]
    (T : V) (R : Finset V) (hdisj : Disjoint R (R.image (· + T)))
    (hcover : R ∪ R.image (· + T) = Finset.univ)
    (χ f : V → ℝ) (hχ : ∀ S : V, χ (S + T) = -χ S) :
    ∑ S : V, χ S * f S = ∑ S ∈ R, χ S * (f S - f (S + T)) := by
  have hinj : Function.Injective (fun S : V => S + T) := add_left_injective T
  calc ∑ S : V, χ S * f S
      = ∑ S ∈ (R ∪ R.image (· + T)), χ S * f S := by rw [hcover]
    _ = (∑ S ∈ R, χ S * f S) + (∑ S ∈ R.image (· + T), χ S * f S) := by rw [Finset.sum_union hdisj]
    _ = (∑ S ∈ R, χ S * f S) + (∑ S ∈ R, χ (S + T) * f (S + T)) := by
        rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    _ = ∑ S ∈ R, (χ S * f S + χ (S + T) * f (S + T)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ S ∈ R, χ S * (f S - f (S + T)) := by
        refine Finset.sum_congr rfl (fun S _ => ?_); rw [hχ S]; ring

#print axioms coset_pairing_doubled
#print axioms coset_pairing_transversal
end YangMills.DualBook
