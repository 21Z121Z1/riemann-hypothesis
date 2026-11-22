import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductLevelStructureEqMkPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivial
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.KerC

theorem ker_zarhinPolarization_of_pullback : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx hv j
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  haveI : IsMonHom la := hla
  have hQ : Q.IsLB := hD1.isLB
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull hz]
    exact (cls_eq_zero_iff (pull_isLB hz _)).2 hx
  have h1 := congrArg (CechPic.pull
    (lift (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then snd T B else 1)) (fst T B) :
      T ⊗ B ⟶ Zob c.A B ⊗ T).left) h0
  rw [← pull_comp, ← Over.comp_left, comp_lift, map_zero, lift_snd_assoc, lift_fst,
    AdjPf.pull_zCls c.isLB hQ d la mu hPQ] at h1
  simp only [AdjPf.zf, Category.assoc, AdjPf.mkZ_pa, AdjPf.mkZ_pb, hv, MonObj.comp_one, MonObj.one_comp,
    evc_one_right hQ hD1.zero, hD1.additive.evc_one hQ, smul_zero, Finset.sum_const_zero, zero_add, add_zero] at h1
  simp only [apply_ite (evc hQ _), evc_one_right hQ hD1.zero, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  refine (hD1.isPerfect hD2).ker_left T _ ((triv_ev_iff hQ _ _).2 ?_)
  let F : (T ⊗ B ⟶ c.A) →* Multiplicative (Pic (T ⊗ B).left) :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hQ a (snd T B))) fun a a' => by
      rw [(isAdditive_iff hQ).1 hD1.additive, ofAdd_add]
  have eF : ∀ a, evc hQ a (snd T B) = Multiplicative.toAdd (F a) := fun _ => rfl
  have ep : fst T B ≫ ∏ i, (x ≫ pa c.A B i) ^ quat d j i = ∏ i, (fst T B ≫ x ≫ pa c.A B i) ^ quat d j i := by
    have := map_prod (AdjPf.pre (G := c.A) (fst T B)) (fun i => (x ≫ pa c.A B i) ^ quat d j i) Finset.univ
    simp only [map_zpow] at this
    exact this
  rw [ep, eF, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← eF]
  exact h1

end GlobalTheory.ZarhinFam.KerC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquations
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section RadialKernelIntegrals

variable {S : Scheme.{0}}

def precompHom {Y Y' G : Over S} [GrpObj G] (f : Y' ⟶ Y) : (Y ⟶ G) →* (Y' ⟶ G) :=
  MonoidHom.mk' (fun a => f ≫ a) (fun a b => MonObj.comp_mul f a b)

def postcompHom {Y G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (Y ⟶ G) →* (Y ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) (fun a b => MonObj.mul_comp a b g)

def evcHom {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (t : Y ⟶ T) :
    (Y ⟶ A) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hM a t)) (fun a b => by
    rw [(isAdditive_iff hM).1 h Y a b t]; rfl)

theorem evc_prod_zpow_left {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) {K : Type} [Fintype K] (a : K → (Y ⟶ A)) (n : K → ℤ) (t : Y ⟶ T) :
    evc hM (∏ k, a k ^ n k) t = ∑ k, n k • evc hM (a k) t := by
  have e := map_prod (evcHom hM h t) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact congrArg Multiplicative.toAdd e

theorem evc_pow_left {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) (a : Y ⟶ A) (n : ℕ) (t : Y ⟶ T) : evc hM (a ^ n) t = n • evc hM a t :=
  congrArg Multiplicative.toAdd (map_pow (evcHom hM h t) a n)

theorem evc_mul_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hM a (b * b') = evc hM a b + evc hM a b' := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', ← evc_swap hM hs', ← evc_swap hM hs']
  exact (isAdditive_iff hs').1 hs Y b b' a

theorem evc_prod_zpow_right {A B Y : Over S} [GrpObj B] [IsCommMonObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) {K : Type} [Fintype K] (a : Y ⟶ A) (b : K → (Y ⟶ B)) (n : K → ℤ) :
    evc hM a (∏ k, b k ^ n k) = ∑ k, n k • evc hM a (b k) := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_prod_zpow_left hs' hs]
  exact Finset.sum_congr rfl fun k _ => by rw [evc_swap hM hs']

theorem evc_pow_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hM a (b ^ n) = n • evc hM a b := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_pow_left hs' hs, evc_swap hM hs']

theorem comp_prod_zpow'' {Y Y' G : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K] (f : Y' ⟶ Y)
    (a : K → (Y ⟶ G)) (n : K → ℤ) : f ≫ ∏ k, a k ^ n k = ∏ k, (f ≫ a k) ^ n k := by
  have e := map_prod (precompHom f) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

theorem prod_zpow_comp'' {Y G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H] {K : Type}
    [Fintype K] (a : K → (Y ⟶ G)) (n : K → ℤ) (g : G ⟶ H) [IsMonHom g] :
    (∏ k, a k ^ n k) ≫ g = ∏ k, (a k ≫ g) ^ n k := by
  have e := map_prod (postcompHom (Y := Y) g) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

end RadialKernelIntegrals

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section KerAux2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  rw [pa, ← Category.assoc, mkZ, lift_fst]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  rw [pb, ← Category.assoc, mkZ, lift_snd]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (p q : Y ⟶ Zob A B) :
    CechPic.pull (lift p q).left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (p ≫ pa A B i) (q ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (p ≫ pa A B i) (q ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (q ≫ pa A B i) (p ≫ pb A B j)) +
      ∑ j, evc hQ (q ≫ pb A B j ≫ mu) (p ≫ pb A B j) := by
  simp only [zCls, map_add, map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

end KerAux2

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx j
  have hQ : IsDual c.A B Q := hZ.2.1
  have hQ' : IsDual B c.A (swap Q) := hZ.2.2.1
  haveI hla : IsMonHom la := hZ.2.2.2.1
  haveI hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hPQ := hZ.2.2.2.2.2.2.2
  have hzP := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
  have h0 : ∀ (Y : Over S) (s : Y ⟶ T) (z : Y ⟶ Zob c.A B),
      CechPic.pull (lift (s ≫ x) z).left (zCls c.A B c.isLB hQ.isLB d mu) = 0 := by
    intro Y s z
    have e := congrArg (CechPic.pull (lift z s).left) ((cls_eq_zero_iff (pull_isLB hzP _)).2 hx)
    rw [cls_pull hzP, cls_zP, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e
    exact e

  have e := h0 (c.A ⊗ T) (snd c.A T)
    (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then fst c.A T ≫ la else 1))
  rw [pull_zCls] at e
  simp only [mkZ_pa', mkZ_pb'] at e
  simp only [← Category.assoc, mkZ_pa', mkZ_pb'] at e
  have t2 : ∀ i, ∑ j', quat d j' i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i)
      (if j' = j then fst c.A T ≫ la else 1) = quat d j i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T ≫ la) :=
    fun i => by
      rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', evc_one_right hQ.isLB hQ.zero, smul_zero]),
        if_pos rfl]
  have t4 : ∑ j', evc hQ.isLB ((if j' = j then fst c.A T ≫ la else 1) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j') =
      evc hQ.isLB ((fst c.A T ≫ la) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', MonObj.one_comp, hQ.additive.evc_one hQ.isLB]),
      if_pos rfl]
  simp only [t2, t4, evc_one_right c.isLB c.rig₂, hQ.additive.evc_one hQ.isLB, smul_zero, Finset.sum_const_zero,
    zero_add, add_zero] at e
  have hPev : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc hQ.isLB p (q ≫ la) := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc hQ.isLB (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ.isLB _)).2 hPQ
    rw [evc, e1, pull_evc, lift_fst, lift_snd_assoc]
  have hPsymm : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc c.isLB q p := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc c.isLB (snd c.A c.A) (fst c.A c.A) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    rw [evc, e1, pull_evc, lift_fst, lift_snd]
  have hQsw : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc hQ.isLB p (q ≫ la) = evc hQ.isLB q (p ≫ la) := by
    intro Y p q
    rw [← hPev, ← hPev, hPsymm]
  refine (hQ.isPerfect hQ').ker_right T _ ((triv_ev_iff hQ.isLB _ _).2 ?_)
  rw [MonObj.comp_mul, ← Category.assoc, comp_prod_zpow'', prod_zpow_comp'', MonObj.comp_pow,
    evc_mul_right hQ.isLB hQ'.additive, evc_prod_zpow_right hQ.isLB hQ'.additive, evc_pow_right hQ.isLB hQ'.additive]
  rw [Category.assoc, hlm, MonObj.comp_pow, Category.comp_id, evc_pow_left hQ.isLB hQ.additive] at e
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQsw, Category.assoc]

end GlobalTheory.ZarhinKerB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivial
section
open Matrix

namespace GlobalTheory.ZarhinFam

theorem zpow_finset_sum' {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ k ∈ s, e k) = ∏ k ∈ s, a ^ e k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, _root_.zpow_add, ih]

theorem prod_prod_zpow_mul {G : Type} [CommGroup G] (P Q : Matrix (Fin 4) (Fin 4) ℤ) (w : Fin 4 → G)
    (a : Fin 4) : ∏ k, (∏ i, w i ^ Q k i) ^ P a k = ∏ i, w i ^ (P * Q) a i := by
  simp_rw [← Finset.prod_zpow, ← _root_.zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, zpow_finset_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem prod_zpow_smul_one {G : Type} [CommGroup G] (c : ℤ) (w : Fin 4 → G) (a : Fin 4) :
    ∏ i, w i ^ (c • (1 : Matrix (Fin 4) (Fin 4) ℤ)) a i = w a ^ c := by
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem zarhin_kernel_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  intro d GA GB _ _ f g hd hgf u v hA hB hC
  have hxx : quat d * (quat d)ᵀ = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_mul_transpose d
  have hxtx : (quat d)ᵀ * quat d = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_transpose_mul d
  have hd1 : d = (d - 1) + 1 := by omega
  have hv : ∀ k, v k = 1 := by
    intro k
    have E : ∏ i, (f (u i) * ∏ j, v j ^ quat d j i) ^ quat d k i = 1 := by
      simp [hA]
    rw [Finset.prod_congr rfl fun i _ => mul_zpow (f (u i)) (∏ j, v j ^ quat d j i) (quat d k i),
      Finset.prod_mul_distrib] at E
    have E2 : ∏ i, (∏ j, v j ^ (quat d)ᵀ i j) ^ quat d k i = v k ^ (((d - 1 : ℕ) : ℤ)) := by
      rw [prod_prod_zpow_mul, hxx, prod_zpow_smul_one]
    simp only [Matrix.transpose_apply] at E2
    have hF : f (∏ i, u i ^ quat d k i) = ∏ i, f (u i) ^ quat d k i := by
      simp [map_prod, map_zpow]
    rw [E2, ← hF, zpow_natCast] at E
    have hBk := hB k
    rw [show v k ^ d = v k ^ (d - 1) * v k by rw [← pow_succ, ← hd1], ← mul_assoc, E, one_mul] at hBk
    exact hBk
  refine ⟨?_, hv⟩
  have hxu := hC hv
  intro l
  have E : ∏ k, (∏ i, u i ^ quat d k i) ^ (quat d)ᵀ l k = 1 := by
    simp [hxu]
  rw [prod_prod_zpow_mul, hxtx, prod_zpow_smul_one, zpow_natCast] at E
  have hfu : f (u l) = 1 := by
    have h := hA l
    simpa [hv] using h
  have hdu : u l ^ d = 1 := by
    rw [← hgf, hfu, map_one]
  rw [show u l ^ d = u l ^ (d - 1) * u l by rw [← pow_succ, ← hd1], E, one_mul] at hdu
  exact hdu

end GlobalTheory.ZarhinFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrderAction_rosati_adjoint : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Adj (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) (GlobalTheory.ZarhinFam.bar d) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (exact GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (intros; apply GlobalTheory.ZarhinFam.AdjPf.adj_actZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrder_isRingAction_on_product : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (exact GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (intros; apply GlobalTheory.ZarhinFam.RAct.actZ_isRAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductLevelStructureEqMkPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProductLevelStructure_eq_mkPoint : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (d h h' : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (κ : Fin 8 → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ), GlobalTheory.ZarhinFam.levZ lev (GlobalTheory.ZarhinFam.incZ A B) (GlobalTheory.ZarhinFam.actZ A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ a = GlobalTheory.ZarhinFam.mkZ A B (fun i => lev (κ (Fin.castAdd 4 i) a)) (fun j => lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
  first | (exact @GlobalTheory.ZarhinFam.levZ_eq_mkZ) | (exact GlobalTheory.ZarhinFam.levZ_eq_mkZ) | (intros; apply GlobalTheory.ZarhinFam.levZ_eq_mkZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFacts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.PtFacts

theorem mkZ_facts : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T T' : Over S} (f : T' ⟶ T) (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (g : T ⟶ GlobalTheory.ZarhinFam.Zob A B) (n : ℕ), f ≫ GlobalTheory.ZarhinFam.mkZ A B u v = GlobalTheory.ZarhinFam.mkZ A B (fun i => f ≫ u i) (fun j => f ≫ v j) ∧ GlobalTheory.ZarhinFam.mkZ A B u v ^ n = GlobalTheory.ZarhinFam.mkZ A B (fun i => u i ^ n) (fun j => v j ^ n) ∧ (GlobalTheory.ZarhinFam.mkZ A B u v = 1 ↔ (∀ i, u i = 1) ∧ ∀ j, v j = 1) ∧ g = GlobalTheory.ZarhinFam.mkZ A B (fun i => g ≫ GlobalTheory.ZarhinFam.pa A B i) (fun j => g ≫ GlobalTheory.ZarhinFam.pb A B j) := by
  intro S A B _ _ _ _ T T' f u v g n
  refine ⟨?_, ?_, ⟨fun h => ⟨fun i => ?_, fun j => ?_⟩, fun ⟨hu, hv⟩ => ?_⟩, ?_⟩
  · apply LevAlg.zob_ext
    · intro i; simp only [Category.assoc, LevAlg.mkZ_pa]
    · intro j; simp only [Category.assoc, LevAlg.mkZ_pb]
  · apply LevAlg.zob_ext
    · intro i; rw [MonObj.pow_comp, LevAlg.mkZ_pa, LevAlg.mkZ_pa]
    · intro j; rw [MonObj.pow_comp, LevAlg.mkZ_pb, LevAlg.mkZ_pb]
  · rw [← LevAlg.mkZ_pa A B u v i, h, MonObj.one_comp]
  · rw [← LevAlg.mkZ_pb A B u v j, h, MonObj.one_comp]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa, MonObj.one_comp, hu]
    · intro j; rw [LevAlg.mkZ_pb, MonObj.one_comp, hv]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa]
    · intro j; rw [LevAlg.mkZ_pb]

end GlobalTheory.ZarhinFam.PtFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClausesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProduct_relation_algebraic_clauses : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  first | (exact @GlobalTheory.ZarhinFam.zRel_alg) | (exact GlobalTheory.ZarhinFam.zRel_alg) | (intros; apply GlobalTheory.ZarhinFam.zRel_alg  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinSymplecticTransferBijectiveModStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod : ∀ (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), 1 ≤ M → GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧ ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  first | (exact @GlobalTheory.ZarhinFam.kappaOK_mod) | (exact GlobalTheory.ZarhinFam.kappaOK_mod) | (intros; apply GlobalTheory.ZarhinFam.kappaOK_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef
section
open Matrix

namespace GlobalTheory.ZarhinFam

theorem zW_symm_blocks (d : ℕ) (i j : Fin 4 ⊕ Fin 4) :
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 i j +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 j i =
    2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1 i j := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.zero_apply, smul_eq_mul]
  all_goals (try simp only [@eq_comm _ b a])
  all_goals (try split_ifs)
  all_goals ring

theorem zarhin_block_posDef {d : ℕ} (hd : 0 < d) :
    (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
      (Int.cast : ℤ → ℝ) |>.PosDef := by
  set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx
  have hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢
    rw [h0]
    split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]
  set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC
  set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'
  have hCC : C' * C = 1 := by
    rw [hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg (C'.mulVec) hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C =
      (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
        (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
    congr 1
    · rw [Matrix.transpose_one, Matrix.one_mul, hxx]; ext i j
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    · simp [hx, Matrix.transpose_map]
    · simp [hx]
    · simp
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

theorem zW_symm_posDef : ∀ (d : ℕ), 0 < d →
    ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  intro d hd
  have hsig : Function.Injective sig := by
    intro a b h; revert a b h; decide
  have h := ((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e := zW_symm_blocks d (sig k) (sig l)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

end GlobalTheory.ZarhinFam
end

