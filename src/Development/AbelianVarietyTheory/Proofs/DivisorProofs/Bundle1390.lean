import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOpenCompact
section
open GlobalTheory.LKCount

noncomputable section
open scoped Classical

namespace GlobalTheory.LKCountPoint

section Gen
variable {G : Type} [Group G]

theorem mem_map_conj {K : Subgroup G} {a z : G} :
    z ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * z * a ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  ext z
  simp only [mem_map_conj, mul_inv_rev, mul_assoc]

theorem map_conj_inf_of_mem {T : Subgroup G} {t : G} (ht : t ∈ T) (K : Subgroup G) :
    (T ⊓ K).map (MulAut.conj t).toMonoidHom = T ⊓ K.map (MulAut.conj t).toMonoidHom := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht)
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht, h2⟩

theorem relIndex_inf_inf_ne_zero (H : Subgroup G) {U K : Subgroup G} (h : U.relIndex K ≠ 0) :
    (H ⊓ U).relIndex (H ⊓ K) ≠ 0 := by
  have := Subgroup.relIndex_inter_ne_zero h H
  rwa [inf_comm U H, inf_comm K H] at this

end Gen

section Prod
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem prod_map_conj (A : Subgroup G₁) (B : Subgroup G₂) (x : G₁ × G₂) :
    (A.prod B).map (MulAut.conj x).toMonoidHom =
      (A.map (MulAut.conj x.1).toMonoidHom).prod (B.map (MulAut.conj x.2).toMonoidHom) := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

theorem twCent_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (a : G₁) (b : G₂) :
    GlobalTheory.BCT.twCent (θ₁.prodMap θ₂) (a, b) = (GlobalTheory.BCT.twCent θ₁ a).prod (GlobalTheory.BCT.twCent θ₂ b) := by
  ext z
  rw [Subgroup.mem_prod]
  show z * (a, b) = (a, b) * (θ₁.prodMap θ₂) z ↔ z.1 * a = a * θ₁ z.1 ∧ z.2 * b = b * θ₂ z.2
  rw [Prod.ext_iff]
  exact Iff.rfl

theorem relIndex_prod (A C : Subgroup G₁) (B D : Subgroup G₂) :
    (A.prod B).relIndex (C.prod D) = A.relIndex C * B.relIndex D := by
  have e : (A.prod B).subgroupOf (C.prod D) =
      ((A.subgroupOf C).prod (B.subgroupOf D)).comap (Subgroup.prodEquiv C D).toMonoidHom := by
    ext z
    exact Iff.rfl
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv C D).surjective,
    Subgroup.index_prod]
  rfl

theorem vol_prod (C₁ H₁ : Subgroup G₁) (C₂ H₂ : Subgroup G₂) :
    vol (C₁.prod C₂) (H₁.prod H₂) = vol C₁ H₁ * vol C₂ H₂ := by
  unfold vol
  rw [relIndex_prod, relIndex_prod]
  push_cast
  rw [div_mul_div_comm]

theorem stab_eq {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = ((K₁.prod K₂).map (MulAut.conj x).toMonoidHom).comap (ι₁.prod ι₂) := by
  rw [prod_map_conj]
  ext g
  exact Iff.rfl

theorem card_stab {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (hι : Function.Injective (ι₁.prod ι₂)) (x : G₁ × G₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ x) =
      Nat.card ((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) := by
  rw [stab_eq, ← Subgroup.map_comap_eq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ hι).toEquiv

theorem finite_inter {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) (h : Finite (stab ι₁ ι₂ K₁ K₂ x)) :
    (((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) :
      Set (G₁ × G₂)).Finite := by
  rw [← Subgroup.map_comap_eq, ← stab_eq, Subgroup.coe_map]
  exact Set.Finite.image _ (Set.toFinite _)

end Prod

section Core
variable {G : Type} [Group G]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext z
  simp [mem_map_conj]

theorem vol_self (A : Subgroup G) : vol A A = 1 := by
  simp [vol, Subgroup.relIndex_self]

theorem fold_sum (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
        ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
          F (Quotient.out q) =
      ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G),
        ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) :=
  GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup Γ' T K F hΓT hF hfin hsupp

theorem massC_ne_zero_of_ne (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 :=
  GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support Γ' T K F hΓT hF hfin hsupp y hy

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Core

end GlobalTheory.LKCountPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSKerRes

section Dictionary

variable {Y : Scheme.{0}} {M N : LB Y} {O W : Y.Opens}

theorem coord_resM (h : W ≤ O) (s : Γ(LB.toMod M, O)) (i : M.ι) :
    LB.coord (Twist.resM (LB.toMod M) h s) i = resG Y (inf_le_inf_right _ h) (LB.coord s i) :=
  LB.coord_map h s i

theorem le_tens (O : Y.Opens) (q : (tens M N).ι) : O ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 ⊓ M.U q.1 :=
  fun _ hy => ⟨⟨hy.1, hy.2.2⟩, hy.2.1⟩

def ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) : Γ(LB.toMod (tens M N), O) :=
  LB.mkSec (fun q => resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1)) fun p q => by
    have h₁ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U p.2 := fun _ hy => ⟨hy.1.1, hy.1.2.2⟩
    have h₂ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 := fun _ hy => ⟨hy.1.1, hy.2.2⟩
    have h₃ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U p.1 := fun _ hy => hy.1.2.1
    have h₄ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U q.1 := fun _ hy => hy.2.1
    have e₁ := congrArg (fun r => resG Y (le_inf le_rfl h₄) (LB.coord r q.1))
      (Twist.coord_rel s p.2 q.2 h₁ h₂ (le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)))
    have e₂ := LB.coord_rel (Twist.coord s p.2) p.1 q.1 (le_inf h₁ h₃) (le_inf h₁ h₄) (le_inf h₃ h₄)
    simp only [coord_resM, LB.coord_smul, map_mul, LB.resG_resG] at e₁
    simp only [LB.resG_resG]
    refine e₂.trans ?_
    rw [e₁, ← mul_assoc]
    refine congrArg (· * _) ?_
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))).symm

theorem coord_ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) (q : (tens M N).ι) :
    LB.coord (ofTwistFun s) q = resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1) := rfl

def ofTwist : Γ(twist (LB.toMod M) N, O) →+ Γ(LB.toMod (tens M N), O) where
  toFun := ofTwistFun
  map_zero' := LB.sec_ext fun q => by
    rw [coord_ofTwistFun, Twist.coord_zero, LB.coord_zero, map_zero, LB.coord_zero]
  map_add' s t := LB.sec_ext fun q => by
    rw [LB.coord_add, coord_ofTwistFun, coord_ofTwistFun, coord_ofTwistFun, Twist.coord_add, LB.coord_add, map_add]

theorem tens_le (O : Y.Opens) (i : M.ι) (j : N.ι) : O ⊓ N.U j ⊓ M.U i ≤ O ⊓ (tens M N).U (i, j) :=
  fun _ hy => ⟨hy.1.1, hy.2, hy.1.2⟩

theorem tens_rel (f : Γ(LB.toMod (tens M N), O)) (i i' : M.ι) (j j' : N.ι) (h : W ≤ O ⊓ (tens M N).U (i, j))
    (h' : W ≤ O ⊓ (tens M N).U (i', j')) (hM : W ≤ M.U i ⊓ M.U i') (hN : W ≤ N.U j ⊓ N.U j') :
    resG Y h (LB.coord f (i, j)) = resG Y hM (M.g i i' : Γ(Y, M.U i ⊓ M.U i')) *
      resG Y hN (N.g j j' : Γ(Y, N.U j ⊓ N.U j')) * resG Y h' (LB.coord f (i', j')) := by
  refine (LB.coord_rel f (i, j) (i', j') h h' (le_inf (h.trans inf_le_right) (h'.trans inf_le_right))).trans ?_
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))

theorem surjective_ofTwist (hM : M.IsLB) (hN : N.IsLB) :
    Function.Surjective (ofTwist : Γ(twist (LB.toMod M) N, O) → Γ(LB.toMod (tens M N), O)) := fun f => by
  let a : ∀ j : N.ι, Γ(LB.toMod M, O ⊓ N.U j) := fun j =>
    LB.mkSec (fun i => resG Y (tens_le O i j) (LB.coord f (i, j))) fun i i' => by
      simp only [LB.resG_resG]
      refine (tens_rel f i i' j j _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.1.2⟩)
        (by exact fun _ hy => ⟨hy.1.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.1.2⟩)).trans ?_
      exact congrArg (· * _) ((congrArg (_ * ·) (LB.resG_g_self hN _ _)).trans (mul_one _))
  have ha : ∀ j i, LB.coord (a j) i = resG Y (tens_le O i j) (LB.coord f (i, j)) := fun _ _ => rfl
  refine ⟨Twist.mkSec a fun j j' => LB.sec_ext fun i => ?_, LB.sec_ext fun q => ?_⟩
  · simp only [coord_resM, LB.coord_smul, ha, LB.resG_resG]
    refine (tens_rel f i i j j' _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.2⟩)
      (by exact fun _ hy => ⟨hy.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.2⟩)).trans ?_
    exact congrArg (· * _) ((congrArg (· * _) (LB.resG_g_self hM _ _)).trans (one_mul _))
  · refine (coord_ofTwistFun _ q).trans ?_
    exact (LB.resG_resG (tens_le O q.1 q.2) (le_tens O q) (LB.coord f q)).trans (LB.resG_self _ _)

variable {k : Type} [CommRing k] (p : Y ⟶ Sp k) {L : LB Y} {n l : ℤ}

def toH0 : Γ(twistZ (LB.toMod M) L n, O) →+ Vanishing.H0 p (tw M L n) O := ofTwist

theorem restricted_section_chart_coords (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι)
    (h : W ≤ O ⊓ (tw M L n).U (twIdx n i j)) (h' : W ≤ O ⊓ L.U j ⊓ M.U i) :
    resG Y h ((toH0 p s).loc (twIdx n i j)) = resG Y h' (LB.coord (Twist.zcoord s j) i) := by
  rw [Twist.zcoord, coord_resM, LB.resG_resG]
  exact LB.resG_resG _ _ _

theorem germ_of_global_section (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι) (y : Y) (hy : y ∈ O)
    (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    H0.germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (toH0 p s) =
      ger y (memInf (memInf hy hj) hi) (LB.coord (Twist.zcoord s j) i) := by
  have h : O ⊓ L.U j ⊓ M.U i ≤ O ⊓ (tw M L n).U (twIdx n i j) := fun _ hz => ⟨hz.1.1, mem_tw_U.2 ⟨hz.2, hz.1.2⟩⟩
  have e := congrArg (ger y (memInf (memInf hy hj) hi)) (restricted_section_chart_coords p s i j h le_rfl)
  rwa [ger_resG, ger_resG] at e

theorem global_section_mul (hM : M.IsLB) (hL : L.IsLB) (w : L.Sec) (h : n + 1 = l) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec w) h).app O s) = mulSec hM hL w h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, germ_of_global_section p _ i j y hy hi hj, germ_of_global_section p _ i j y hy hi hj,
      Twist.zcoord_mulSecOfEq_app, LB.coord_smul, map_mul, ger_resG, ger_resG, Twist.zfun_zofSec]

theorem exists_local (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) (h : n + 1 = l)
    (s : Γ(twistZ (LB.toMod M) L l, ⊤)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) (y : Y) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin d → Γ(twistZ (LB.toMod M) L n, W)),
      (twistZ (LB.toMod M) L l).presheaf.map (homOfLE le_top).op s =
        ∑ i, (Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec (t i)) h).app W (m i) := by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf hi hj)
  have hVi : V.1 ≤ M.U i := e.trans inf_le_left
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ ⊤ ⊓ (tw M L l).U (twIdx l i j) := fun _ hz => ⟨trivial, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf le_top hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hV, fun a => (Twist.zchartEquiv hL n j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL l j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [coord_resM]
  erw [Twist.zcoord_resM]
  rw [coord_resM, LB.resG_resG, LB.resG_resG]

end Dictionary

section Main

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Main

theorem exists_global {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hY : IsProjOver (GlobalTheory.strHom k Y))
    (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) {n l : ℤ} (h : n + 1 = l)
    (hreg : RegSeq hL (LB.toMod M) (List.ofFn t)) (hvan : VanishFrom L (LB.toMod M) 0) (hd : (d : ℤ) ≤ n + 1)
    (f : Vanishing.H0 p (tw M L l) ⊤) (hf : VanishesTo (cutIdeal hL t) 1 f) :
    ∃ μ : Fin d → Vanishing.H0 p (tw M L n) ⊤, f = ∑ i, mulSec hM hL (t i) h (μ i) := by
  subst h
  obtain ⟨σ, rfl⟩ : ∃ σ : Γ(twistZ (LB.toMod M) L (n + 1), ⊤), toH0 p σ = f :=
    surjective_ofTwist hM (Twist.isLB_lbZPow hL _) f
  have := (VB.isVB_toMod hM).isFiniteQC
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_global_combination_of_local_regular_ideal k Y hY L hL d t (LB.toMod M) 0 n hreg hvan ((zero_add _).trans_le hd) σ
    (exists_local p hM hL t rfl σ hf)
  refine ⟨fun i => toH0 p (m i), (congrArg (toH0 p) hm).trans ?_⟩
  exact (map_sum (toH0 p) _ _).trans (Finset.sum_congr rfl fun i _ => global_section_mul p hM hL _ rfl (m i))

theorem kerRes : Quoted → KerRes := by
  intro Q K _ _ G hnef hbig s hs l hl f hf
  obtain ⟨⟨f, rfl⟩, hv⟩ := mem_Fil.1 hf
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨g, hg, hreg⟩ := GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros K G s hs _ hB
  have hv' := vanishesTo_of_isUnit G s g hg ((vanishesTo_restr_iff hs.inU le_top).1 hv)
  have hproj : IsProjOver (GlobalTheory.strHom K G.Y) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  obtain ⟨μ, e⟩ := exists_global hproj G.str hB G.isLB _ (Nat.cast_succ l).symm hreg (GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist Q K G hnef hbig)
    (by exact_mod_cast hl) f hv'
  refine ⟨fun j => H0.restr le_top (∑ i, g i j • μ i), fun j => ⟨_, rfl⟩, ?_⟩
  have e' (i) : H0.restr (le_top : G.U ≤ ⊤) (mulSec hB G.isLB (G.comb (∑ j, g i j • s j)) (Nat.cast_succ l).symm (μ i)) =
      G.mulW l (∑ j, g i j • s j) (H0.restr le_top (μ i)) := by
    rw [G.mulW_apply, mulSec, mulSec, ProdChart.restr_mul, H0.restr_ofSec]
  rw [e, map_sum]
  simp only [e', map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

end GlobalTheory.HSKerRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SmoothCharDet

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

theorem isSmoothChar_of_detChar_apow_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  intro k _ _ _ _ n hn ν s P hP hν
  let i0 : Fin n := ⟨0, hn⟩
  let d : kˣ →* GL (Fin n) k :=
    (diagHom (k := k) (n := Fin n)).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i0)
  have hval : Continuous fun x : kˣ => ((d x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    show Continuous fun x : kˣ => diagonal fun i => (((Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x) i : kˣ) : k)
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).comp (continuous_mulSingle (A := fun _ : Fin n => kˣ) i0)))
  have hd : Continuous d := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have := hval.comp continuous_inv
    simpa [Function.comp_def, map_inv] using this
  have hdet : ∀ x : kˣ, gdet (d x) = x := fun x => by
    show Matrix.GeneralLinearGroup.det (diagGL (Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x)) = x
    rw [det_diagGL]
    simp
  have hU : (d : kˣ → GL (Fin n) k) ⁻¹' (P ∩ (KO k (Fin n) : Set (GL (Fin n) k))) ∈ 𝓝 (1 : kˣ) := by
    refine hd.continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact Filter.inter_mem hP (isOpen_KO.mem_nhds (one_mem _))
  refine Subgroup.isOpen_of_mem_nhds ν.ker (Filter.mem_of_superset hU fun x hx => ?_)
  have h1 := hν _ hx.1
  rw [apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.2), mul_one, hdet] at h1
  exact MonoidHom.mem_ker.2 (Units.ext h1)

end GlobalTheory.SmoothCharDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulDetSpanSupLeDetSpanLatticeStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_detSpan_sup_le_detSpan_lattice : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F), π • u ∈ N → ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v}, π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  first | exact @GlobalTheory.DetColon.smul_detSpan_sup_le | exact GlobalTheory.DetColon.smul_detSpan_sup_le | (intros; apply GlobalTheory.DetColon.smul_detSpan_sup_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushout
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem pinch_main : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x z hxz
  let T := Sp (TrivSqZeroExt R M)
  let i : Sp R ⟶ T := spMap (TrivSqZeroExt.fstHom R R M).toRingHom
  let j : Sp (TrivSqZeroExt B M) ⟶ T := spMap β
  have hcov0 := fun q => exists_basicOpen_inl (M := M) x q
  have EO := GlobalTheory.T.trivSqZeroExt_pinch_exists_extend_basicOpen R B M β hβ X x z hxz
  have UO := GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique R B M β hβ X x
  have RES : ∀ {Y' : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X) (w : Y' ⟶ X),
      f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w → f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
    intro Y' f' V V' h g w hg
    have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
    rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]
  let Idx := {p : Γ(T, ⊤) × X.affineOpens // i ⁻¹ᵁ T.basicOpen p.1 ≤ x ⁻¹ᵁ p.2.1}
  have hcov : TopologicalSpace.IsOpenCover (fun p : Idx => T.basicOpen p.1.1) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro q _
    obtain ⟨s, U, hq, hle⟩ := hcov0 q
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(s, U), hle⟩, hq⟩
  let 𝒰 := T.openCoverOfIsOpenCover _ hcov
  choose g hg using fun p : Idx => EO p.1.1 p.1.2 p.2
  have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
    intro a b
    have hP := isPullback_opens_inf (T.basicOpen a.1.1) (T.basicOpen b.1.1)
    change pullback.fst (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g a =
      pullback.snd (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g b
    rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    refine UO _ (a.1.1 * b.1.1) (T.basicOpen_mul _ _).symm a.1.2 ((i.preimage_mono inf_le_left).trans a.2) _ _
      (RES i _ _ x (hg a).1) (RES i _ _ x (hg b).1) ?_
    rw [RES j _ _ z (hg a).2, RES j _ _ z (hg b).2]
  let z₀ := 𝒰.glueMorphisms g hc
  have hz₀ : ∀ a : Idx, (T.basicOpen a.1.1).ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
  have hi : i ≫ z₀ = x := by
    have hcovR : TopologicalSpace.IsOpenCover (fun p : Idx => i ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp R).openCoverOfIsOpenCover _ hcovR) _ _ fun a => ?_
    change (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ i ≫ z₀ = (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ x
    rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι i (le_rfl), Category.assoc]
  have hj : j ≫ z₀ = z := by
    have hcovA : TopologicalSpace.IsOpenCover (fun p : Idx => j ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp (TrivSqZeroExt B M)).openCoverOfIsOpenCover _ hcovA) _ _ fun a => ?_
    change (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ j ≫ z₀ = (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ z
    rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j (le_rfl), Category.assoc]
  refine ⟨z₀, ⟨hi, hj⟩, fun z₁ ⟨h1, h2⟩ => ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
  change (T.basicOpen a.1.1).ι ≫ z₁ = (T.basicOpen a.1.1).ι ≫ z₀
  rw [hz₀ a]
  refine UO _ a.1.1 rfl a.1.2 a.2 _ _ ?_ (hg a).1 ?_
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h1]
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h2, (hg a).2]

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCaseStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZeroLifting_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  first | exact @GlobalTheory.SqLift.sqLifting_of_noetherian | exact GlobalTheory.SqLift.sqLifting_of_noetherian | (intros; apply GlobalTheory.SqLift.sqLifting_of_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometryStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  first | exact @GlobalTheory.IsomPhi.phi_map | exact GlobalTheory.IsomPhi.phi_map | (intros; apply GlobalTheory.IsomPhi.phi_map <;> assumption)
end

