import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.adjoint_of :
    PairCalc → TorsFree → Adjoint := by
  intro hPC hTF p _ D R _ b N k _ s c o o' ψ ψ' hψ hψ' hc T x y
  have hpos : 0 < c := hψ.pos
  obtain ⟨a₁, a₂, -, -, hsim⟩ := hPC p D R b N _ s o
  obtain ⟨a₁', a₂', -, -, -⟩ := hPC p D R b N _ s o'
  obtain ⟨-, hmon, -, -, hiso, -⟩ := hψ
  have hsim' := (hsim o' ψ c).1 hiso
  haveI := hmon
  haveI := hψ'

  have hsym : ∀ (q : Obj b N s) {Y : Over (Sp k)} (u v : Y ⟶ q.A),
      evc q.isLB u v = evc q.isLB v u := by
    intro q Y u v
    have h1 := (GlobalTheory.CechPic.cls_eq_iff q.isLB (pull_isLB q.isLB _)).2 q.symm
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift u v).left) h1
    rw [GlobalTheory.AbDual.cls_ev q.isLB, GlobalTheory.AbDual.pull_evc, lift_snd, lift_fst] at h2
    exact h2

  have hL1 := pull_isLB o'.isLB (lift (fst o.A o'.A ≫ ψ) (snd o.A o'.A)).left
  have hL2 := pull_isLB o.isLB (lift (fst o.A o'.A) (snd o.A o'.A ≫ ψ')).left
  have hL := LB.isLB_div hL1 hL2
  have cL := GlobalTheory.CechPic.cls_div hL1 hL2 hL
  have hev : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc hL u v = evc o'.isLB (u ≫ ψ) v - evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [GlobalTheory.AbDual.evc, cL, map_sub, GlobalTheory.AbDual.cls_ev o'.isLB, GlobalTheory.AbDual.cls_ev o.isLB,
      GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]
  have add₁ := (GlobalTheory.AbDual.isAdditive_iff o.isLB).1 a₁
  have add₁' := (GlobalTheory.AbDual.isAdditive_iff o'.isLB).1 a₁'
  have add₂ := (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 a₂
  have add₂' := (GlobalTheory.BirigidLift.isAdditive_swap_iff o'.isLB).1 a₂'
  have bL₁ : IsAdditive (A := o.A) (T := o'.A) _ := (GlobalTheory.AbDual.isAdditive_iff hL).2 fun Y u u' v ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₁', add₁]
    abel
  have bL₂ : IsAdditive (swap _) := (GlobalTheory.BirigidLift.isAdditive_swap_iff hL).2 fun Y u v v' ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₂', add₂]
    abel

  have hpow : ∀ {Y : Over (Sp k)} (u : Y ⟶ o'.A) (v : Y ⟶ o'.A) (n : ℕ),
      evc o'.isLB u (v ^ n) = n • evc o'.isLB u v := by
    intro Y u v n
    induction n with
    | zero =>
      have e := add₂' Y u 1 1
      rw [_root_.mul_one] at e
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 e
    | succ n ih => rw [pow_succ, add₂', ih, succ_nsmul]
  have hcm : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      c • evc o'.isLB (u ≫ ψ) v = c • evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← hsim' Y u (v ≫ ψ'), ← hpow, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
  have hcls : GlobalTheory.CechPic.cls _ hL = evc hL (fst o.A o'.A) (snd o.A o'.A) := by
    rw [GlobalTheory.AbDual.evc, lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have hz : GlobalTheory.CechPic.cls _ hL = 0 := hTF k o.A o'.A o.ab o'.ab _ hL bL₁ bL₂ c hpos (by
    rw [hcls, hev, smul_sub, hcm, sub_self])
  have hmain : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc o'.isLB (u ≫ ψ) v = evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← sub_eq_zero, ← hev, GlobalTheory.AbDual.evc, hz, map_zero]
  exact ⟨hmain x y, by rw [hsym o', hmain, hsym o]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobIsog
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isIso_spMap_pow {K : Type} [Field K] [IsAlgClosed K] (φ : K →+* K) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ a, φ a = a ^ n) : IsIso (spMap φ) := by
  have hbij : Function.Bijective φ := by
    refine ⟨φ.injective, fun x => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x hn
    exact ⟨z, by rw [hφ, hz]⟩
  haveI : IsIso (CommRingCat.ofHom φ) := (RingEquiv.ofBijective φ hbij).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

private theorem cls_hecke_pow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  simp [GlobalTheory.CechPic.pull_id]

private theorem square_map_fst_left {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (g : A ⟶ B) : sq2 g ≫ (fst B B).left = (fst A A).left ≫ g.left := by
  simp only [sq2, ← Over.comp_left, lift_fst]

private theorem square_map_snd_left {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (g : A ⟶ B) : sq2 g ≫ (snd B B).left = (snd A A).left ≫ g.left := by
  simp only [sq2, ← Over.comp_left, lift_snd]

private theorem tensor_left_ext {S X : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (u v : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have hw : u ≫ (A ⊗ A).hom = v ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, h₁, Category.assoc]
  have key : (Over.homMk u rfl : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk v hw.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa using h₁
    · ext
      simpa using h₂
  simpa using congrArg CommaMorphism.left key

theorem UpperTheory.Gal.crystallineComparison.Mod.frobIsog_of :
    FrobHom → FrobFin → PicFrob → QuasiInv → FrobIsog := by
  intro hHom hFin hPic hQI p _ D R _ b N f κ _ _ _ s φ hφ hs o
  have hp : Nat.Prime p := Fact.out
  have hκ := GlobalTheory.SS.FrobField.cast_zero_sp κ (p := p) (CharP.cast_eq_zero κ p)
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N (Sp κ) (Sp κ) s (spMap φ) o
  revert o₁ m₁
  rw [hs]
  intro o₁ m₁
  have hA := GlobalTheory.SS.FrobField.cast_zero_of_hom o.A.hom hκ
  obtain ⟨F, hFm, hFφ, hFk⟩ := hHom p f hp κ φ hφ o.A o₁.A m₁.φ m₁.cart hA
  have hn : 0 < p ^ f := pow_pos hp.pos f
  haveI : IsIso (spMap φ) := isIso_spMap_pow φ hn hφ
  haveI : IsIso m₁.φ := m₁.cart.1.isIso_fst_of_isIso
  have hFsp : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hFφ' : ∀ {Z : Scheme} (h : o.A.left ⟶ Z),
      Over.Hom.left F ≫ m₁.φ ≫ h = GlobalTheory.SS.FrobField.absFrob o.A.left p f hp hA ≫ h := by
    intro Z h
    rw [← Category.assoc, hFφ]
  have hpt : ∀ (a : 𝟙_ (Over (Sp κ)) ⟶ o.A),
      Over.Hom.left a ≫ Over.Hom.left F ≫ m₁.φ = spMap φ ≫ Over.Hom.left a := by
    intro a
    rw [hFφ, ← GlobalTheory.SS.FrobField.absFrob_nat (Over.Hom.left a) p f hp hκ hA]
    exact congrArg (· ≫ Over.Hom.left a) hFsp
  have hact : ∀ c, o.act.act c ≫ F = F ≫ o₁.act.act c := by
    intro c
    ext1
    rw [← cancel_mono m₁.φ]
    simp only [Over.comp_left, Category.assoc, m₁.act, hFφ, hFφ']
    exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hA hA).symm
  have heta : ∀ x, o₁.eta x = o.eta x ≫ F := by
    intro x
    ext1
    rw [← cancel_mono m₁.φ, m₁.eta, Over.comp_left, Category.assoc, hpt]
  have hG := GlobalTheory.SS.FrobField.cast_zero_of_hom (G2 o.A).hom hκ
  have hsq : sq2 F ≫ m₁.φ₂ = GlobalTheory.SS.FrobField.absFrob (G2 o.A).left p f hp hG := by
    apply tensor_left_ext
    · rw [Category.assoc, m₁.sq.1, ← Category.assoc, square_map_fst_left, Category.assoc, hFφ]
      exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hG hA).symm
    · rw [Category.assoc, m₁.sq.2, ← Category.assoc, square_map_snd_left, Category.assoc, hFφ]
      exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hG hA).symm
  have hpol : Nonempty (LBIso (Hecke.lbPow o.P (p ^ f)) (o₁.P.pull (sq2 F))) := by
    have h1 : (Hecke.lbPow o.P (p ^ f)).IsLB :=
      LB.isLB_linComb o.isLB (fun _ : Fin (p ^ f) => 𝟙 _) (fun _ => (1 : ℤ))
    have h2 := pull_isLB o₁.isLB (sq2 F)
    have h3 := pull_isLB o.isLB m₁.φ₂
    have e1 : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m₁.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) := by
      rw [(GlobalTheory.CechPic.cls_eq_iff o₁.isLB h3).mpr m₁.pol, GlobalTheory.CechPic.cls_pull]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff h1 h2).mp ?_⟩
    rw [cls_hecke_pow o.isLB, GlobalTheory.CechPic.cls_pull o₁.isLB, e1, ← GlobalTheory.CechPic.pull_comp, hsq, hPic]
  have hFl : Over.Hom.left F = GlobalTheory.SS.FrobField.absFrob o.A.left p f hp hA ≫ inv m₁.φ := by
    rw [← hFφ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hlft : LocallyOfFiniteType o.A.hom := by
    haveI := o.ab
    haveI : Smooth o.A.hom := IsAbelianScheme.smooth
    infer_instance
  obtain ⟨hfin, hsurj⟩ := hFin p f hp κ o.A.left o.A.hom hlft hA
  have hfin' : IsFinite (Over.Hom.left F) := by
    rw [hFl]
    infer_instance
  have hsurj' : Surjective (Over.Hom.left F) := by
    rw [hFl]
    infer_instance
  have hker : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp κ) (g : Over.mk z ⟶ o.A),
      g ≫ F = 1 → g = 1 := by
    intro K _ _ z g hg
    have hT := GlobalTheory.SS.FrobField.cast_zero_of_hom z hκ
    haveI : CharP K p := charP_of_injective_ringHom (Spec.preimage z).hom.injective p
    haveI : ExpChar K p := ExpChar.prime hp
    have hτ : ∀ c : K, iterateFrobenius K p f c = c ^ p ^ f := by
      intro c
      simp [iterateFrobenius_def]
    haveI : IsIso (spMap (iterateFrobenius K p f)) := isIso_spMap_pow _ hn hτ
    have hFK : GlobalTheory.SS.FrobField.absFrob (Over.mk z).left p f hp hT = spMap (iterateFrobenius K p f) :=
      GlobalTheory.SS.FrobField.absFrob_spec K p f hp hT _ hτ
    have hk := (hFk _ g).mp hg hT
    rw [hFK, cancel_epi] at hk
    exact Over.OverMorphism.ext hk
  obtain ⟨ψ', hψm, e1, e2⟩ := hQI p D R b N κ s (p ^ f) hn o o₁ F hFm hfin' hsurj' hpol hker
  refine ⟨o₁, m₁, F, ⟨⟨f, rfl⟩, hFm, hact, heta, hpol, ψ', hψm, e1, e2⟩, ?_, hFk⟩
  intro a
  rw [Over.comp_left, Category.assoc]
  exact hpt a
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobPass
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable def frPt {κ Λ Λ' : Type} [Field κ] [CommRing Λ] [CommRing Λ'] [Algebra κ Λ] [Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ') : algPt κ Λ' ⟶ algPt κ Λ :=
  Over.homMk (spMap σ) (by
    change spMap σ ≫ spMap (algebraMap κ Λ) = spMap (algebraMap κ Λ')
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ])

private theorem frob_mid (hI : InfE) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {r : ℤ} {κ : Type} [Field κ] {s : Sp κ ⟶ Sp R} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} {d : ℕ}
    (hrep : RepAlg o.A (UKer r o ψ) d)
    (hcard : Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [IsLocalRing Λ'] [Algebra κ Λ] [algΛ' : Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ')
    (ε : Λ →ₐ[κ] κ) (ε' : Λ' →+* κ) (h1 : ∀ c, ε' (algebraMap κ Λ' c) = c)
    (h2 : ε'.comp σ = ε.toRingHom) (g : algPt κ Λ ⟶ o.A)
    (hK : ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) (hinf : Inf ε g)
    (hker : spMap σ ≫ (g ≫ ψ).left = spMap σ ≫ (1 : algPt κ Λ ⟶ o'.A).left) :
    spMap σ ≫ g.left = spMap σ ≫ (1 : algPt κ Λ ⟶ o.A).left := by
  let ε'' : Λ' →ₐ[κ] κ := { ε' with commutes' := h1 }
  have hfl : (frPt σ hσ).left = spMap σ := rfl
  have hone : ∀ {X Y A : Over (Sp κ)} [GrpObj A] (f : X ⟶ Y), f ≫ (1 : Y ⟶ A) = 1 := by
    intro X Y A _ f
    simp [Hom.one_def]
  have hcomp : spMap ε''.toRingHom ≫ spMap σ = spMap ε.toRingHom := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h2]
  have hgψ : (frPt σ hσ ≫ g) ≫ ψ = 1 := by
    rw [← hone (frPt σ hσ)]
    ext1
    simp only [Over.comp_left] at hker ⊢
    rw [hfl, Category.assoc]
    exact hker
  obtain ⟨e, he⟩ := hK
  have hP : UKer r o ψ (algPt κ Λ') (frPt σ hσ ≫ g) := by
    refine ⟨hgψ, e, ?_⟩
    intro a ha
    rw [Category.assoc, he a ha, hone]
  have hinf' : Inf ε'' (frPt σ hσ ≫ g) := by
    unfold Inf at hinf ⊢
    rw [Over.comp_left, hfl, ← Category.assoc, hcomp]
    exact hinf
  have h0 := hI κ o.A (UKer r o ψ) d hrep hcard Λ' ε'' (frPt σ hσ ≫ g) hP hinf'
  have h0' := congrArg Over.Hom.left (h0.trans (hone (frPt σ hσ)).symm)
  simp only [Over.comp_left] at h0'
  exact h0'

theorem UpperTheory.Gal.crystallineComparison.Mod.frobPass_of :
    InfE → FrobPass := by
  intro hI p _ D R _ b N r f κ _ _ _ s o o' ψ hψ d hrep hcard
  haveI := hψ
  have hp : Nat.Prime p := Fact.out
  have hone' : ∀ {X A B : Over (Sp κ)} [GrpObj A] [GrpObj B] (h : A ⟶ B) [IsMonHom h], (1 : X ⟶ A) ≫ h = 1 := by
    intro X A B _ _ h _
    simp [Hom.one_def]
  let φ : κ ≃+* κ := iterateFrobeniusEquiv κ p f
  have hφ : ∀ c : κ, φ c = c ^ p ^ f := fun c => rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    have h0 := GlobalTheory.SS.FrobField.cast_zero_sp κ (CharP.cast_eq_zero κ p)
    have e := GlobalTheory.SS.FrobField.absFrob_spec κ p f hp h0 φ.toRingHom hφ
    have hk : spMap φ.toRingHom ≫ g.left = spMap φ.toRingHom ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
      rw [← e]
      exact hg h0
    have hinv : spMap φ.symm.toRingHom ≫ spMap φ.toRingHom = 𝟙 _ := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      simp
    ext1
    calc g.left = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ g.left := by rw [hinv, Category.id_comp]
      _ = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
        rw [Category.assoc, hk, ← Category.assoc]
      _ = _ := by rw [hinv, Category.id_comp]
  · intro Λ _ _ _ ε g hK hinf
    have hΛ : (p : Λ) = 0 := by
      rw [← map_natCast (algebraMap κ Λ), CharP.cast_eq_zero, map_zero]
    let τ := GlobalTheory.SS.FrobField.powHom Λ p f hp hΛ
    have hτ : ∀ c : Λ, τ c = c ^ p ^ f := fun c => rfl
    let ε' : Λ →+* κ := φ.symm.toRingHom.comp ε.toRingHom
    have h2 : ε'.comp τ = ε.toRingHom := by
      ext x
      show φ.symm (ε (x ^ p ^ f)) = ε x
      rw [map_pow, ← hφ, RingEquiv.symm_apply_apply]
    constructor
    · intro hk h
      have e := GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h τ hτ
      have hker : spMap τ ≫ (g ≫ ψ).left = spMap τ ≫ (1 : algPt κ Λ ⟶ o'.A).left := by
        rw [← e]
        exact hk h
      have h1 : ∀ c : κ, ε' (@algebraMap κ Λ _ _ (τ.comp (algebraMap κ Λ)).toAlgebra c) = c := by
        intro c
        show (ε'.comp τ) (algebraMap κ Λ c) = c
        rw [h2]
        exact ε.commutes c
      have := frob_mid hI hrep hcard (Λ' := Λ) (algΛ' := (τ.comp (algebraMap κ Λ)).toAlgebra) τ rfl ε ε' h1 h2 g
        ⟨hK.choose, hK.choose_spec⟩ hinf hker
      rw [← e] at this
      exact this
    · intro hk h
      have h' := hk h
      rw [Over.comp_left, ← Category.assoc, h', Category.assoc, ← Over.comp_left, hone']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsoOfKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization

variable {S : Scheme.{0}}

private lemma pow_comp' {T A B : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  exact (IsMonHom.monoidHom f T).map_pow x n

private lemma comp_pow' {T' T A : Over S} [GrpObj A] (t : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    t ≫ (x ^ n) = (t ≫ x) ^ n := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih => simp only [pow_succ, Hom.mul_def, comp_lift_assoc, ih]

private lemma self_pow {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    f ^ n = ((𝟙 A) ^ n) ≫ f := by
  rw [pow_comp', Category.id_comp]

private lemma cancel (hDiv : DivC) {A₀ A B : Over S} [GrpObj A₀] [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {c : ℕ} (hc : 0 < c) (ψ : A₀ ⟶ A) (ψ' : A ⟶ A₀) (e : ψ' ≫ ψ = (𝟙 A) ^ c)
    (u v : A ⟶ B) [IsMonHom u] [IsMonHom v] (h : ψ ≫ u = ψ ≫ v) : u = v := by
  have h2 : ψ' ≫ ψ ≫ u = ψ' ≫ ψ ≫ v := by rw [h]
  rw [← Category.assoc, ← Category.assoc, e, ← self_pow, ← self_pow] at h2
  exact (hDiv S A B hA c hc).2 u v inferInstance inferInstance h2

private lemma factor (hDiv : DivC) {A₀ A₁ A₂ : Over S} [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₁] [IsCommMonObj A₁]
    [GrpObj A₂] [IsCommMonObj A₂] (h₀ : IsAbelianScheme A₀) (h₁ : IsAbelianScheme A₁) {c : ℕ} (hc : 0 < c)
    (ψ₁ : A₀ ⟶ A₁) (ψ₁' : A₁ ⟶ A₀) (ψ₂ : A₀ ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₁'] [IsMonHom ψ₂]
    (u : ψ₁ ≫ ψ₁' = (𝟙 A₀) ^ c) (v : ψ₁' ≫ ψ₁ = (𝟙 A₁) ^ c)
    (hk : ∀ (T : Over S) (g : T ⟶ A₀), g ≫ ψ₁ = 1 → g ≫ ψ₂ = 1) :
    ∃ ρ : A₁ ⟶ A₂, IsMonHom ρ ∧ ρ ^ c = ψ₁' ≫ ψ₂ ∧ ψ₁ ≫ ρ = ψ₂ := by
  obtain ⟨ν, hν, hνc⟩ := (hDiv S A₁ A₂ h₁ c hc).1 (ψ₁' ≫ ψ₂) inferInstance (by
    intro T g hg
    have : (g ≫ ψ₁') ≫ ψ₁ = 1 := by
      rw [Category.assoc, v, comp_pow', Category.comp_id, hg]
    rw [← Category.assoc]
    exact hk T _ this)
  haveI := hν
  refine ⟨ν, hν, hνc, ?_⟩
  refine (hDiv S A₀ A₂ h₀ c hc).2 (ψ₁ ≫ ν) ψ₂ inferInstance inferInstance ?_
  rw [← comp_pow', hνc, ← Category.assoc, u, ← self_pow]

variable {A T Y : Over S} [GrpObj A]

private lemma evc_pow_left {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (a : Y ⟶ A) (t : Y ⟶ T) (n : ℕ) :
    evc hM (a ^ n) t = n • evc hM a t := by
  induction n with
  | zero => simp [IsAdditive.evc_one hM h]
  | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hM).1 h, ih, succ_nsmul]

private lemma evc_add_right {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap (A := A) (B := B) P))
    (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hP a (b * b') = evc hP a b + evc hP a b' := by
  have hs : (swap (A := A) (B := B) P).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hP _
  rw [← GlobalTheory.AbDual.evc_swap hP hs, ← GlobalTheory.AbDual.evc_swap hP hs, ← GlobalTheory.AbDual.evc_swap hP hs]
  exact (GlobalTheory.AbDual.isAdditive_iff hs).1 h Y b b' a

private lemma evc_pow_right {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap (A := A) (B := B) P))
    (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hP a (b ^ n) = n • evc hP a b := by
  have hs : (swap (A := A) (B := B) P).IsLB := LB.isLB_pull hP _
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, ← GlobalTheory.AbDual.evc_swap hP hs]
    exact IsAdditive.evc_one hs h a
  | succ n ih => rw [pow_succ, evc_add_right hP h, ih, succ_nsmul]

end UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization

open UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization in
theorem UpperTheory.Gal.crystallineComparison.Mod.isoOfKer_of :
    PairCalc → Adjoint → DivC → TorsFree → IsoOfKer := by
  intro hPC hAdj hDiv hTF
  intro p _ D R _ b N k _ s c o o₁ o₂ ψ₁ ψ₂ h1 h2 hker
  have hc : 0 < c := h1.pos
  obtain ⟨-, hm1, hact1, heta1, hpol1, ψ₁', hψ₁', u1, v1⟩ := h1
  obtain ⟨-, hm2, hact2, heta2, hpol2, ψ₂', hψ₂', u2, v2⟩ := h2
  haveI := hm1
  haveI := hm2
  haveI := hψ₁'
  haveI := hψ₂'
  obtain ⟨ρ, hρ, -, hρ1⟩ := factor hDiv o.ab o₁.ab hc ψ₁ ψ₁' ψ₂ u1 v1 (fun T g h => (hker T g).1 h)
  obtain ⟨ρ', hρ', -, hρ2⟩ := factor hDiv o.ab o₂.ab hc ψ₂ ψ₂' ψ₁ u2 v2 (fun T g h => (hker T g).2 h)
  haveI := hρ
  haveI := hρ'
  have hrr : ρ ≫ ρ' = 𝟙 o₁.A :=
    cancel hDiv o₁.ab hc ψ₁ ψ₁' v1 _ _ (by rw [← Category.assoc, hρ1, hρ2, Category.comp_id])
  have hr'r : ρ' ≫ ρ = 𝟙 o₂.A :=
    cancel hDiv o₂.ab hc ψ₂ ψ₂' v2 _ _ (by rw [← Category.assoc, hρ2, hρ1, Category.comp_id])
  have hP0 := hPC p D R b N (Sp k) s o
  have hP1 := hPC p D R b N (Sp k) s o₁
  have hP2 := hPC p D R b N (Sp k) s o₂
  have e1 := (hP0.2.2.2.2 o₁ ψ₁ c).1 hpol1
  have e2 := (hP0.2.2.2.2 o₂ ψ₂ c).1 hpol2
  have hLp : (o₂.P.pull (sq2 ρ)).IsLB := LB.isLB_pull o₂.isLB _
  have hL : ((o₂.P.pull (sq2 ρ)).div o₁.P).IsLB := LB.isLB_div hLp o₁.isLB
  have hlift : ∀ {Y : Over (Sp k)} (a t : Y ⟶ o₁.A), (lift a t).left ≫ sq2 ρ = (lift (a ≫ ρ) (t ≫ ρ)).left := by
    intro Y a t
    show (lift a t).left ≫ (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left = _
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  have hevL : ∀ {Y : Over (Sp k)} (a t : Y ⟶ o₁.A),
      evc hL a t = evc o₂.isLB (a ≫ ρ) (t ≫ ρ) - evc o₁.isLB a t := by
    intro Y a t
    unfold GlobalTheory.AbDual.evc
    rw [GlobalTheory.CechPic.cls_div hLp o₁.isLB hL, map_sub, GlobalTheory.CechPic.cls_pull o₂.isLB _ hLp,
      ← GlobalTheory.CechPic.pull_comp, hlift]
  have hadd1 := (GlobalTheory.AbDual.isAdditive_iff o₁.isLB).1 hP1.1
  have hadd2 := (GlobalTheory.AbDual.isAdditive_iff o₂.isLB).1 hP2.1
  have hmulρ : ∀ {Y : Over (Sp k)} (a a' : Y ⟶ o₁.A), (a * a') ≫ ρ = (a ≫ ρ) * (a' ≫ ρ) := by
    intro Y a a'
    exact (IsMonHom.monoidHom ρ Y).map_mul a a'
  have hLadd : IsAdditive ((o₂.P.pull (sq2 ρ)).div o₁.P) := by
    rw [GlobalTheory.AbDual.isAdditive_iff hL]
    intro Y a a' t
    rw [hevL, hevL, hevL, hmulρ, hadd2, hadd1]
    abel
  have hsL : (swap ((o₂.P.pull (sq2 ρ)).div o₁.P)).IsLB := LB.isLB_pull hL _
  have hLsadd : IsAdditive (swap ((o₂.P.pull (sq2 ρ)).div o₁.P)) := by
    rw [GlobalTheory.AbDual.isAdditive_iff hsL]
    intro Y b' b'' a
    rw [GlobalTheory.AbDual.evc_swap hL hsL, GlobalTheory.AbDual.evc_swap hL hsL, GlobalTheory.AbDual.evc_swap hL hsL, hevL, hevL, hevL, hmulρ,
      evc_add_right o₂.isLB hP2.2.1, evc_add_right o₁.isLB hP1.2.1]
    abel
  have hz : ∀ {Y : Over (Sp k)} (z w : Y ⟶ o.A), evc hL (z ≫ ψ₁) (w ≫ ψ₁) = 0 := by
    intro Y z w
    rw [hevL, Category.assoc, Category.assoc, hρ1, e1, e2, sub_self]
  have hxc : ∀ {Y : Over (Sp k)} (x : Y ⟶ o₁.A), x ^ c = (x ≫ ψ₁') ≫ ψ₁ := by
    intro Y x
    rw [Category.assoc, v1, comp_pow', Category.comp_id]
  have huniv : evc hL (fst o₁.A o₁.A) (snd o₁.A o₁.A) = GlobalTheory.CechPic.cls _ hL := by
    unfold GlobalTheory.AbDual.evc
    rw [lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have key : evc hL ((fst o₁.A o₁.A) ^ c) ((snd o₁.A o₁.A) ^ c) = 0 := by
    rw [hxc, hxc]
    exact hz _ _
  rw [evc_pow_left hL hLadd, evc_pow_right hL hLsadd, smul_smul, huniv] at key
  have hcls := hTF k o₁.A o₁.A o₁.ab o₁.ab _ hL hLadd hLsadd (c * c) (Nat.mul_pos hc hc) key
  rw [GlobalTheory.CechPic.cls_div hLp o₁.isLB hL, sub_eq_zero] at hcls
  have hpol : LBIso o₁.P (o₂.P.pull (sq2 ρ)) := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB hLp).1 hcls.symm
  haveI : IsIso ρ.left := ⟨⟨ρ'.left, by rw [← Over.comp_left, hrr, Over.id_left],
    by rw [← Over.comp_left, hr'r, Over.id_left]⟩⟩
  refine ⟨⟨ρ.left, sq2 ρ, ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩, ⟨?_, ?_⟩, ?_, hpol, ?_⟩, ?_⟩
  · intro T x y x₀ y₀ hx hy
    let i : Over.mk (T.hom ≫ 𝟙 (Sp k)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have hx' : x₀ = i ≫ x ≫ ρ := by
      ext1
      rw [hx]
      simp [i]
    have hy' : y₀ = i ≫ y ≫ ρ := by
      ext1
      rw [hy]
      simp [i]
    have hm : (i ≫ x ≫ ρ) * (i ≫ y ≫ ρ) = i ≫ (x * y) ≫ ρ := by
      rw [hmulρ x y, Hom.mul_def, Hom.mul_def, comp_lift_assoc]
    rw [hx', hy', hm]
    simp [i]
  · show (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left ≫ _ = _
    rw [← Over.comp_left, lift_fst, Over.comp_left]
  · show (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left ≫ _ = _
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  · intro a
    haveI := o₁.act.hom a
    haveI := o₂.act.hom a
    have h : o₁.act.act a ≫ ρ = ρ ≫ o₂.act.act a :=
      cancel hDiv o₁.ab hc ψ₁ ψ₁' v1 _ _ (by
        rw [← Category.assoc, ← hact1 a, Category.assoc, hρ1, hact2 a, ← hρ1, Category.assoc])
    rw [← Over.comp_left, h, Over.comp_left]
  · intro y
    rw [← Over.comp_left, heta1 y, Category.assoc, hρ1, ← heta2 y, Category.id_comp]
  · rw [← Over.comp_left, hρ1]
end

