import Erdos1152.FiniteData
import Erdos1152.Boundary

/-! Finite stages of the construction, including data shared by different rows. -/

open Polynomial MeasureTheory Set

namespace Erdos1152

structure Stage (X : NodeArray) where
  rows : Finset ℕ
  data : FiniteData
  nodes_mem : ∀ n ∈ rows, ∀ i, X.node n i ∈ data.domain

namespace Stage

def empty (X : NodeArray) : Stage X where
  rows := ∅
  data := ⟨∅, fun _ => 0, by simp⟩
  nodes_mem := by simp

def Extends {X : NodeArray} (S T : Stage X) : Prop :=
  S.rows ⊆ T.rows ∧ S.data.Extends T.data

def Above {X : NodeArray} (S : Stage X) (N : ℕ) : Prop := ∀ n ∈ S.rows, N ≤ n

def Fits {X : NodeArray} (S : Stage X) (r : ℕ → ℕ) (p : ℕ → ℝ[X]) : Prop :=
  ∀ n ∈ S.rows, (p n).natDegree ≤ n + 1 + r n ∧
    ∀ i, (p n).eval (X.node n i : ℝ) = S.data.value (X.node n i)

theorem Extends.refl {X : NodeArray} (S : Stage X) : S.Extends S :=
  ⟨Subset.rfl, FiniteData.Extends.refl S.data⟩

theorem Extends.trans {X : NodeArray} {S T U : Stage X}
    (hST : S.Extends T) (hTU : T.Extends U) : S.Extends U :=
  ⟨hST.1.trans hTU.1, hST.2.trans hTU.2⟩

theorem Fits.restrict {X : NodeArray} {S T : Stage X} {r : ℕ → ℕ} {p : ℕ → ℝ[X]}
    (hp : T.Fits r p) (hST : S.Extends T) : S.Fits r p := by
  intro n hn
  refine ⟨(hp n (hST.1 hn)).1, fun i => ?_⟩
  rw [(hp n (hST.1 hn)).2 i, hST.2.2 _ (S.nodes_mem n hn i)]

theorem Extends.lowSet_subset {X : NodeArray} {S T : Stage X} (hST : S.Extends T)
    (p : ℕ → ℝ[X]) (H : ℝ) : commonLowSet T.rows p H ⊆ commonLowSet S.rows p H := by
  rintro x ⟨hx, hpx⟩
  exact ⟨hx, fun n hn => hpx n (hST.1 hn)⟩

theorem boundary_cover {X : NodeArray} (S : Stage X) (r : ℕ → ℕ)
    (p : ℕ → ℝ[X]) (hp : S.Fits r p) (H : ℝ) :
    ∃ B : Finset ℝ, frontier (commonLowSet S.rows p H) ⊆ (B : Set ℝ) ∧
      B.card ≤ 2 + 2 * ∑ n ∈ S.rows, (n + 1 + r n) := by
  obtain ⟨B, hB, hc⟩ := commonLowSet_boundary_cover S.rows p H
  refine ⟨B, hB, hc.trans ?_⟩
  gcongr with n hn
  exact (hp n hn).1

theorem continuous_extension_fits {X : NodeArray} (S : Stage X) (r : ℕ → ℕ) :
    ∃ g : ContinuousFunction, ‖g‖ ≤ 1 ∧ ∀ p : ℕ → ℝ[X],
      (∀ n ∈ S.rows, X.Interpolates r g n (p n)) → S.Fits r p := by
  obtain ⟨g, hg, he⟩ := S.data.exists_continuous_extension
  refine ⟨g, hg, fun p hp n hn => ⟨(hp n hn).1, fun i => ?_⟩⟩
  rw [(hp n hn).2 i, he _ (S.nodes_mem n hn i)]

end Stage

end Erdos1152
