import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0439
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0152
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

section Small
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem row_small_of_mul_eq_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (l : Fin n) (M N : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hMN : M * N = 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) (hM : ∀ j, j ≠ l → Valued.v (M l j) < 1)
    (hl : Valued.v (M l l) = 1) (j : Fin n) (hj : j ≠ l) : Valued.v (N l j) < 1 := by
  have e := congrFun (congrFun hMN l) j
  rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm hj), ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at e
  have e2 : M l l * N l j = -∑ i ∈ Finset.univ.erase l, M l i * N i j := eq_neg_of_add_eq_zero_left e
  have h3 : Valued.v (∑ i ∈ Finset.univ.erase l, M l i * N i j) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i hi => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hN i j)) (hM i (Finset.ne_of_mem_erase hi))
  have h4 := congrArg Valued.v e2
  rw [Valuation.map_neg, map_mul, hl, one_mul] at h4
  rw [h4]
  exact h3

theorem val_eq_one_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c)
    (hc : c ≠ 0) : Valued.v z = 1 := by
  obtain ⟨r, rfl, hr⟩ := h
  have hr0 : r ∉ P.asIdeal := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hr0
  have e : z = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) +
      (z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [ha]; exact hr), ha]

theorem prV_sigR_eq (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a b => simp [prV, sigR]

variable [StarRing E]

theorem bc_prV_mem_UPts (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (AfE F E)}
    (hk : k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := by
  have hg' : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR_eq]
  have hJ : ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [Matrix.one_apply]
  rw [h1, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Small

theorem map_conj_levStab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E)) (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (E ⊗[F] v.adicCompletion F)), k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → k ∈ stabGL (baseDualV hc n ST v) → k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj k).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST v k hU h1 h2 h3
  have key : ∀ g : GL (Fin n) (E ⊗[F] v.adicCompletion F), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) →
      g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → g ∈ stabGL (baseDualV hc n ST v) →
      g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) →
      ∀ x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v),
      g * x * g⁻¹ ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
    intro g gU gL gD gK x hx
    have hgl : g ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) := Subgroup.mem_inf.2 ⟨gU, gL⟩
    obtain ⟨hxl, hxD, hxf⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgl hxl) (inv_mem hgl), ⟨mul_mem (mul_mem gD hxD) (inv_mem gD), fun y => ?_⟩⟩
    have hz : ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) ∈
        baseDualV hc n ST v := ((inv_mem gD : g⁻¹ ∈ stabGL (baseDualV hc n ST v)) _).1 y.2
    have h4 := hxf ⟨_, hz⟩
    simp only [fLoc, Submodule.mkQ_apply] at h4 ⊢
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h4 ⊢
    simp only [Submodule.coe_subtype, Submodule.coe_sub] at h4 ⊢
    have e : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) -
        (y : Fin n → E ⊗[F] v.adicCompletion F) =
        (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) -
          ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) := by
      have e1 : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F)) = (y : Fin n → E ⊗[F] v.adicCompletion F) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) =
          (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F))) := by
        simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [Matrix.mulVec_sub, e2, e1]
    rw [e]
    exact (gK _).1 h4
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key k hU h1 h2 h3 x hx
  · intro x hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · have := key k⁻¹ (inv_mem hU) (inv_mem h1) (inv_mem h2) (inv_mem h3) x hx
      rwa [inv_inv] at this
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group

set_option maxHeartbeats 1000000 in

theorem basePt_facts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (k : GL (Fin n) (AfE F E)) (c : DiaG E ST), (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧ (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧ ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST π hB k c ⟨p₀, hk, hk0⟩ hrow
  classical
  have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
  have hU : k ∈ UAd hc n := hk.uni
  have hkc := hk.lat
  rw [hk0] at hkc
  have hsingle : ∀ j, (Pi.single j 1 : Fin n → AfE F E) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := fun j => by
    refine (mem_latS_std _).2 fun i => ?_
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hInv : ∀ i j, ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have := (mem_latS_std _).1 ((hkc _).1 (hsingle j)) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hK : ∀ i j, ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have h1 : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((k : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hsingle j
      have := (mem_latS_std _).1 ((hkc _).2 h1) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hvI : ∀ (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E), y ∈ Formalism.L2.Herm.intAf F E → Valued.v (adAt F P y) ≤ 1 :=
    fun P y hy => (mem_rInt_iff F E y).1 hy P
  have hsm : ∀ P ∈ ST, ∀ j, j ≠ lastIdx n →
      Valued.v (adAt F P ((k : Matrix (Fin n) (Fin n) (AfE F E)) (lastIdx n) j)) < 1 := by
    intro P hP j hj
    have hr := fun j' => hrow ⟨P, hP⟩ (lastIdx n) j' hl
    refine row_small_of_mul_eq_one (lastIdx n) (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P))
      ((k : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)) ?_ (fun i j => hvI P _ (hK i j)) (fun j' hj' => ?_) ?_ j hj
    · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := hr j'
      rw [if_neg hj'] at this
      exact DilPt.hasRes_lt_one this
    · have h5 := hr (lastIdx n)
      rw [if_pos rfl] at h5
      have := P.isPrime
      exact val_eq_one_of_hasRes h5 (Units.ne_zero _)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧
      bc (prV (E := E) v) k ∈ stabGL (baseDualV hc n ST v) ∧
      bc (prV (E := E) v) k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
    intro v
    refine GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices hc n hB v _ (bc_prV_mem_UPts hc v hU)
      ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hK i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hK _ j) (fun P hP => hsm P hP j hj)⟩ ?_
    rw [← map_inv]
    refine ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hInv i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hInv _ j) (fun P hP => ?_)⟩
    have := hrow ⟨P, hP⟩ (lastIdx n) j hl
    rw [if_neg hj] at this
    exact DilPt.hasRes_lt_one this
  refine ⟨hU, fun v => ⟨bc_prV_mem_UPts hc v hU, (hloc v).1⟩, fun x => ?_,
    fun v _ => map_conj_levStab hc n ST v _ (bc_prV_mem_UPts hc v hU) (hloc v).1 (hloc v).2.1 (hloc v).2.2⟩
  rw [GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST), GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST)]
  refine forall_congr' fun v => ?_
  have e : (fun i => prV (E := E) v ((k.1 *ᵥ x) i)) =
      ((bc (prV (E := E) v) k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun i => prV (E := E) v (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [e]
  exact ((hloc v).1 _).symm

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLattices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section OrbF

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

theorem image_eq_iff_frStab {P : HeightOneSpectrum (𝓞 X.E)} (C : Set (Sp X.E n)) (g : ↥(GLint X.E n P)) :
    (fun v => g.1 v) '' C = C ↔ g ∈ frStab P C := by
  rw [mem_frStab]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e] at hv
      obtain ⟨u, hu, huv⟩ := hv
      rwa [← g.1.injective huv]
    · intro hv
      rw [← e]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨g.1.symm v, (h _).1 ?_, LinearEquiv.apply_symm_apply g.1 v⟩
      rw [LinearEquiv.apply_symm_apply]
      exact hv

def frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) : FrmG Λ Θ :=
  (g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, cutQ_grp_le _ _ g.2.2.2⟩)

theorem ya_frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) (q : PtY ST SG Q y) :
    (ya Λ Θ (frLift Λ Θ C D g) q).1.1 = g • q.1.1 := rfl

end OrbF

end GlobalTheory.Mem.Col2.ChEx

namespace GlobalTheory.Mem.Col2.ChEx

theorem clsF_bij : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq _ hact hdet hsur hnorm c₀ p hp
  constructor
  · rintro ⟨c, h⟩ ⟨c', h'⟩ e
    obtain ⟨h1, h2, h3⟩ := (hp c).1 h
    obtain ⟨h1', h2', h3'⟩ := (hp c').1 h'
    apply Subtype.ext
    show c = c'
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' e)
    have hb : bar (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = bar (rp Λ Θ p₀ pref c') :=
      (bar_ya_eq_iff _ _ _ _).2 fun w => by rw [h2']; exact (mem_chG.1 g.2.1.2).2 w
    have hq : cq (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = cq (rp Λ Θ p₀ pref c') := by
      funext P
      rw [hact, h3']
      exact (image_eq_iff_frStab _ _).2 ((mem_cutQ_grp.1 g.2.2.2).2 P)
    have e2 : ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c') = rp Λ Θ p₀ pref c :=
      hdet _ _ (by rw [ya_frLift]; exact hg) (hb.trans (h2'.trans h2.symm)) (hq.trans (h3'.trans h3.symm))
    have e3 := cl_ya Λ Θ p₀ pref c₀.1 (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')
    rw [e2] at e3
    have e4 := cl_rp Λ Θ p₀ pref c
    have e5 := cl_rp Λ Θ p₀ pref c'
    have t : ∀ b b' : β, b = b' → ∀ q : PtY ST SG Q y, (stR Λ Θ p₀ pref).cl b q = (stR Λ Θ p₀ pref).cl b' q := by
      rintro b _ rfl q
      rfl
    exact e4.symm.trans ((t _ _ h1 _).trans (e3.trans ((t _ _ h1' _).symm.trans e5)))
  · intro z
    induction z using Quotient.inductionOn' with
    | h d =>
      obtain ⟨r', h1, h2, h3⟩ := hsur (rp Λ Θ p₀ pref c₀) d
      obtain ⟨hb, hq⟩ := hnorm c₀.1 _ _ h2.symm h3.symm
      rw [cl_rp] at hb hq
      refine ⟨⟨(stR Λ Θ p₀ pref).cl c₀.1 r', (hp _).2 ⟨rfl, hb.symm, hq.symm⟩⟩, ?_⟩
      obtain ⟨g, hg⟩ := exists_ya Λ Θ p₀ pref c₀.1 r'
      rw [hg] at hb hq
      have hb' : bar (ya (Λ c₀.1) (Θ c₀.1) g r') = bar r' := hb.symm.trans h2.symm
      have hq' : cq (ya (Λ c₀.1) (Θ c₀.1) g r') = cq r' := hq.symm.trans h3.symm
      rw [bar_ya_eq_iff, h2] at hb'
      have hC : ∀ P : Q, g.2.2.1 P ∈ frStab P.1 (cq (rp Λ Θ p₀ pref c₀) P) := fun P => by
        rw [← h3, ← image_eq_iff_frStab]
        have := congrFun hq' P
        rwa [hact] at this
      let g' : UF X.E n × chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)) × (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀))).grp :=
        (g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, hb'⟩⟩, ⟨g.2.2.1, mem_cutQ_grp.2 ⟨g.2.2.2, hC⟩⟩)
      refine Quotient.sound' (MulAction.orbitRel_apply.2 ⟨g', ?_⟩)
      show g' • d = (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl c₀.1 r')).1.1
      rw [hg, ← h1]
      rfl

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelIffFramesOnPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem frStab_iff_image {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} (g : ↥(GLint E n P)) :
    g ∈ frStab P C ↔ (fun v => g.1 v) '' C = C := by
  constructor
  · intro h
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      have e : g.1 ((g⁻¹).1 v) = v := LinearEquiv.apply_symm_apply g.1 v
      refine ⟨(g⁻¹).1 v, ?_, e⟩
      have h' := h ((g⁻¹).1 v)
      rw [e] at h'
      exact h'.1 hv
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, e⟩ := hv
      rwa [← g.1.injective e]
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩

end SlopeTestRemainingChoices

theorem lev_iff_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar r = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq r = D → ∀ (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)}, g ∈ UAd hc n → g * s ∈ UAd hc n → ∀ (p : DecoF X.E n ST SG Q), FrExact q g r.1.1 → FrExact q (g * s) p → (s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r) := by
  intro X n ST SG Q y _ hc cq hact Λ Θ r C hC D hD q g s hg hgs p hr hp
  have hmul : ∀ P : Q, q.at P (g * s) = q.at P g * q.at P s := fun P => by simp only [QLoc.at, map_mul]
  have hat : ∀ P : Q, bc (q.phi P) (qGL n (r.1.1.fr P)) * q.at P s = bc (q.phi P) (qGL n (p.fr P)) := fun P => by
    rw [← hr.2 P, ← hp.2 P, hmul]
  have hcq : ∀ κ : FrmG Λ Θ, (∀ P : Q, κ.2.2.1 P ∈ frStab P.1 (D P)) ↔ cq (ya Λ Θ κ r) = cq r := by
    intro κ
    rw [funext_iff]
    refine forall_congr' fun P => ?_
    rw [hact Λ Θ κ r P, hD, frStab_iff_image]
  constructor
  · intro hs
    obtain ⟨hsU, hsQ⟩ := (mem_levUQ q _).1 hs
    have h1 := act_of_mem hc n _ 1 hg ⟨s, hsU⟩
    rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1] at h1
    have h2 := mem_chG.1 ((Formalism.L2.Col.levRed hc n ST SG _ ⟨s, hsU⟩)⁻¹).2
    have hN : ∀ (P : Q) (x : Sp X.E n), x ∈ p.deco.1.at P.1 ↔ x ∈ r.1.1.deco.1.at P.1 := by
      intro P x
      rw [h1]
      exact (mem_localization_gmap P.1 ((1 : UF X.E n) : Sp X.E n ≃ₗ[X.E] Sp X.E n) r.1.1.deco.1.N x).trans Iff.rfl
    let t : GLQ X.E n Q := fun P => ⟨(r.1.1.fr P)⁻¹ * p.fr P, by
      show ∀ x, _ ↔ _
      intro x
      have A := r.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x)
      have e : r.1.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x) = p.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [e] at A
      exact A.symm.trans ((hN P _).symm.trans (p.2 P x))⟩
    have hs_at : ∀ P : Q, q.at P s = bc (q.phi P) (qGL n (t P).1) := fun P => by
      rw [eq_inv_mul_of_mul_eq (hat P)]
      show _ = bc (q.phi P) (qGL n ((r.1.1.fr P)⁻¹ * p.fr P))
      simp only [qGL, map_mul, map_inv]
    have ht : ∀ P : Q, t P ∈ (cutQ Θ D P).H := fun P => by
      refine (q.U_rat P (t P)).1 ?_
      have h' := hsQ P
      rw [hs_at P] at h'
      exact h'
    have hθ : (fun P => (t P)⁻¹ : GLQ X.E n Q) ∈ Θ.grp := fun P _ => inv_mem (Subgroup.mem_inf.1 (ht P)).1
    let κ : FrmG Λ Θ := (1, ⟨_, h2.1⟩, ⟨_, hθ⟩)
    refine ⟨κ, map_one _, ?_, (bar_ya_eq_iff _ _ _ _).2 ?_, (hcq κ).1 fun P => inv_mem (Subgroup.mem_inf.1 (ht P)).2⟩
    · apply Subtype.ext
      apply Prod.ext
      · exact h1.symm
      · funext P
        show 1 * r.1.1.1.2 P * (((t P)⁻¹)⁻¹).1 = p.1.2 P
        rw [inv_inv, one_mul]
        exact mul_inv_cancel_left (r.1.1.fr P) (p.fr P)
    · rw [hC]
      exact h2.2
  · rintro ⟨⟨γ, h, θ⟩, h1, h2, h3, h4⟩
    have : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
    subst this
    have hdeco : p.deco = ((1 : UF X.E n), h.1) • r.1.1.deco := by
      rw [← h2]
      rfl
    obtain ⟨hJ, hred⟩ := red_of_act hc n 1 hg hgs h.1 (by rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1, hdeco])
    have hsU : s ∈ levU hc n ST SG (chG Λ C) := (mem_levU hc n ST SG _).2 ⟨hJ, by
      rw [hred]
      refine inv_mem (mem_chG.2 ⟨h.2, ?_⟩)
      rw [← hC]
      exact (bar_ya_eq_iff _ _ _ _).1 h3⟩
    refine (mem_levUQ q _).2 ⟨hsU, fun P => ?_⟩
    have hfr : p.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      rw [← h2]
      show 1 * r.1.1.1.2 P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
      rfl
    have hs_at : q.at P s = bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := by
      rw [eq_inv_mul_of_mul_eq (hat P), hfr]
      simp only [qGL, map_mul, map_inv, inv_mul_cancel_left]
    rw [hs_at]
    refine (q.U_rat P ((θ.1 P)⁻¹)).2 ?_
    exact inv_mem (Subgroup.mem_inf.2 ⟨θ.2 P trivial, (hcq (1, h, θ)).2 h4 P⟩)

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChange
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in

theorem frsF_ya_symm {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) (hP : P.1 ∉ Pr.vGs) (y : Sp X.E (R.N j)) :
    (frsF sel mu (ya Λ Θ g r).1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm (g.1.1 y) =
      (g.2.2.1 P).1 ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y) := by
  rw [LinearEquiv.symm_apply_eq]
  have e1 : (⟨P.1, (Finset.mem_union.mp (Finset.mem_union_right _ P.2)).resolve_left hP⟩ : QE sel (mu : Chr X.F X.E X.K)) = P :=
    Subtype.ext rfl
  simp only [frsF, dif_neg hP, e1]
  show _ = (g.1.1 * r.1.1.1.2 P * ((g.2.2.1 P)⁻¹).1) ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y))
  have e2 : ((g.2.2.1 P)⁻¹).1 ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y)) = (r.1.1.1.2 P).symm y := by
    show (g.2.2.1 P).1.symm ((g.2.2.1 P).1 _) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2]
  show g.1.1 y = g.1.1 ((r.1.1.1.2 P) ((r.1.1.1.2 P).symm y))
  rw [LinearEquiv.apply_symm_apply]

theorem invActs_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ Λ Θ g r P
  have hP := hQ P.1 P.2
  ext z
  simp only [cqOf, cosetIn, Set.mem_setOf_eq, Set.mem_image, if_neg hP]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨(g.2.2.1 P).1.symm z, ⟨y, hy, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    rw [frsF_ya_symm Λ Θ g r P hP y] at hz
    rw [← (g.2.2.1 P).2]
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨z0, ⟨y, hy, hz⟩, rfl⟩
    refine ⟨g.1.1 y, ⟨y, hy, rfl⟩, ?_⟩
    rw [frsF_ya_symm Λ Θ g r P hP y, ← map_sub, ← map_smul]
    exact ((g.2.2.1 P).2 _).2 hz

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetTwistPrimeEmptyOrCoset
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem cqOf_empty_or_coset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)), GlobalTheory.Mem.Col2.ChEx.cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} := by
  intro X Pr R sel S mu cst u j hQ r P
  classical
  have hP : P.1 ∉ Pr.vGs := hQ P.1 P.2
  by_cases hj : j + 1 = R.m
  · right
    obtain ⟨y0, -, hY⟩ := r.mem_ybSet hj
    have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ (by
      rw [Nat.cast_ne_zero]
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.1.ne_bot)
    refine ⟨(frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0, (qOf P.1 : X.E) ^ cst.M, hq, ?_⟩
    ext x
    simp only [cqOf, cosetIn, Set.mem_setOf_eq, if_neg hP]
    constructor
    · rintro ⟨y, hy, hx⟩
      rw [hY] at hy
      have h1 := (mem_locLat _ _ _ _).1 hy ⟨P.1, Finset.mem_union_right _ P.2⟩
      simp only [if_neg hP, zpow_natCast] at h1
      have h2 := (GlobalTheory.ColPeriod.TopTwist.frsF_mem' sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩ hP
        (((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y -
          (frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0))).1 (by
        rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact h1)
      have h3 := Submodule.add_mem _ hx h2
      convert h3 using 1
      rw [← smul_add]
      congr 1
      abel
    · intro hx
      exact ⟨y0, by rw [hY]; simp, hx⟩
  · left
    have h1 : r.1.2 = ∅ := by
      have := r.2
      rwa [ysAt_ys_of_ne _ _ _ hj] at this
    ext x
    simp [cqOf, cosetIn, h1]

end GlobalTheory.Mem.Col2.ChEx
end

