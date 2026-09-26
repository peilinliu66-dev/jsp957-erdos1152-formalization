import Erdos1152.Nodes
import Mathlib.Topology.TietzeExtension

/-! Compatible finite node assignments and their continuous extensions. -/

open Polynomial Set

namespace Erdos1152

structure FiniteData where
  domain : Finset Segment
  value : Segment → ℝ
  bounded : ∀ x ∈ domain, |value x| ≤ 1

namespace FiniteData

def Extends (a b : FiniteData) : Prop :=
  a.domain ⊆ b.domain ∧ ∀ x ∈ a.domain, b.value x = a.value x

theorem Extends.refl (a : FiniteData) : a.Extends a := ⟨Subset.rfl, fun _ _ => rfl⟩

theorem Extends.trans {a b c : FiniteData} (hab : a.Extends b) (hbc : b.Extends c) :
    a.Extends c := by
  refine ⟨hab.1.trans hbc.1, fun x hx => ?_⟩
  rw [hbc.2 x (hab.1 hx), hab.2 x hx]

/-- Every compatible finite assignment bounded by one extends with the same bound. -/
theorem exists_continuous_extension (a : FiniteData) :
    ∃ g : ContinuousFunction, ‖g‖ ≤ 1 ∧ ∀ x ∈ a.domain, g x = a.value x := by
  let f : C(a.domain, ℝ) := ⟨fun x => a.value x, continuous_of_discreteTopology⟩
  have hf : ∀ x : a.domain, f x ∈ Icc (-1 : ℝ) 1 := by
    intro x
    exact abs_le.mp (a.bounded x x.property)
  obtain ⟨g, hg, he⟩ := f.exists_extension_forall_mem_of_isClosedEmbedding hf
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by constructor <;> norm_num⟩)
    a.domain.finite_toSet.isClosed.isClosedEmbedding_subtypeVal
  refine ⟨g, ?_, ?_⟩
  · exact (ContinuousMap.norm_le g (by norm_num)).mpr (fun x => abs_le.mpr (hg x))
  · intro x hx
    exact congrFun he (⟨x, hx⟩ : a.domain)

/-- Add data on new nodes while retaining every earlier assigned value. -/
noncomputable def append (a : FiniteData) (T : Finset Segment) (v : Segment → ℝ)
    (hv : ∀ x ∈ T \ a.domain, |v x| ≤ 1) : FiniteData where
  domain := a.domain ∪ T
  value x := if x ∈ a.domain then a.value x else v x
  bounded x hx := by
    classical
    by_cases ha : x ∈ a.domain
    · simpa [ha] using a.bounded x ha
    · have hxT : x ∈ T := (Finset.mem_union.mp hx).resolve_left ha
      simpa [ha] using hv x (Finset.mem_sdiff.mpr ⟨hxT, ha⟩)

theorem extends_append (a : FiniteData) (T : Finset Segment) (v : Segment → ℝ)
    (hv : ∀ x ∈ T \ a.domain, |v x| ≤ 1) : a.Extends (a.append T v hv) := by
  classical
  exact ⟨Finset.subset_union_left, fun x hx => by simp [append, hx]⟩

theorem append_new_value (a : FiniteData) (T : Finset Segment) (v : Segment → ℝ)
    (hv : ∀ x ∈ T \ a.domain, |v x| ≤ 1) {x : Segment} (hx : x ∉ a.domain) :
    (a.append T v hv).value x = v x := by
  classical
  simp [append, hx]

end FiniteData

end Erdos1152
