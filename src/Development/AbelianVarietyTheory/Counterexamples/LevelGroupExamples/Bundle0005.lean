import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.DetRootRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_baseRing_of_conjugation_fixed_tensor {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (htr : ∀ x, ∃ t, algebraMap F E t = x + σ x) (y : R ⊗[F] E) (hy : sigR R σ y = y) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = y := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [hy] at ht
  show ((2 : F)⁻¹ • t) ⊗ₜ (1 : E) = y
  rw [← TensorProduct.smul_tmul', ← ht, ← two_smul F y, smul_smul]
  norm_num

theorem sigR_algebraMap {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (a : R) : sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  show a ⊗ₜ σ 1 = a ⊗ₜ 1
  rw [map_one]

theorem det_bc {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    (Formalism.UG.bc φ g).1.det = φ g.1.det := by
  rw [RingHom.map_det]; rfl

theorem inclR_injective {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : Function.Injective (inclR (F := F) (E := E) R) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective

theorem fixed_mem_range (y : AE D) (hy : cA D y = y) : ∃ a, algebraMap (AF D.host.F) (AE D) a = y :=
  exists_baseRing_of_conjugation_fixed_tensor D.sp.cm.sig
    (fun x => (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])) y hy

theorem fixed_iff_idF (y : (AE D)ˣ) : cA D (y : AE D) = y ↔ ∃ a, idF D a = y := by
  constructor
  · intro hy
    have hy' : cA D ((y⁻¹ : (AE D)ˣ) : AE D) = (y⁻¹ : (AE D)ˣ) := by
      have h1 : cA D (y : AE D) * cA D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hy] at h1
      exact (Units.inv_eq_of_mul_eq_one_right h1).symm
    obtain ⟨a, ha⟩ := fixed_mem_range _ hy
    obtain ⟨b, hb⟩ := fixed_mem_range _ hy'
    have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
      Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
    have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
    exact ⟨Units.mkOfMulEqOne a b hab, Units.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact sigR_algebraMap D.sp.cm.sig (a : AF D.host.F)

end GlobalTheory.DetRootRows
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.PowSqEqOneOfKilledBy
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RootsSplitTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.SplittingOfRoots

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem zCard_pos (Dw : Datum H) {n : ℕ} (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M) :
    0 < Λ.zCard N (Dw.p + Dw.q) := by
  obtain ⟨zz, -, -, h⟩ := GlobalTheory.ZCount.exists_class_representatives E H Dw n Λ N hU hL.1.pos (hL.2.2.trans inf_le_left)
  obtain ⟨i, -⟩ := h (fun _ => 0) (fun mu _ cm _ i => ⟨0, by simp⟩)
  exact i.pos

theorem pow_sq_eq_one_of_killedBy {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (h : KilledBy Xo (l.Mb ^ 2) t) :
    t ^ (l.M ^ 2) = 1 := by
  have hle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  have hm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
    rw [Nat.cast_pow]; exact Ideal.pow_mem_pow (hle (Ideal.mem_span_singleton_self _)) 2
  have := h _ hm
  rw [GlobalTheory.ZhStable.act_natCast] at this
  simpa [MonObj.comp_pow] using this

theorem geoExhaust_of_field {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G))
    (hf : ∀ (k : Type) [Field k] (x : Sp k ⟶ Xo.X)
      (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (w i)) → GeoInj Xo x w → ∀ a, InZh Xo Λ N a → ∃ i, w i = a)
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo x0 z) : GeoExhaust Xo Λ N x0 z := by
  intro k _ ψ g hgl a ha
  obtain ⟨hp₁, -, hp₃, -⟩ := GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  obtain ⟨i, hi⟩ := hf k _ (fun i b => g ≫ z i b) (fun i => hp₁ _ _ g _ (hz i))
    (hp₃ _ _ _ _ ψ g hgl _ z hg) a ha
  exact ⟨i, fun b => (congrFun hi b).symm⟩

theorem zSplits_of (hL : Laws)
    (hs : ∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M →
      ∃ (B : Type) (_ : CommRing B) (φ : S →+* B)
        (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)),
        φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z)
    (hf : ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M → ∀ (k : Type) [Field k] (x : Sp k ⟶ Xo.X)
      (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (w i)) → GeoInj Xo x w → ∀ a, InZh Xo Λ N a → ∃ i, w i = a) : ZSplits Xo c := by
  intro n Λ N hU hLev S _ _ y
  obtain ⟨B, _, φ₁, z, hφ, hz, hg⟩ := hs S y.x n Λ N hU hLev
  let _ : Algebra c.F B := (φ₁.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { φ₁ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c S B φ y
  have hx : y'.x = spMap φ₁ ≫ y.x := hy'.1
  have key : ∀ x : Sp B ⟶ Xo.X, x = spMap φ₁ ≫ y.x → ∃ w, IsSplitBy Xo Λ N x w := by
    rintro _ rfl
    exact ⟨z, hz, hg, geoExhaust_of_field Xo Λ N _ z (hf n Λ N hU hLev) hz hg⟩
  obtain ⟨w, hw⟩ := key _ hx
  exact ⟨B, inferInstance, inferInstance, φ, y', w, hφ, hy', hw⟩

end GlobalTheory.RootsSplitTest
end
end

