import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0176
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

private theorem gm_id_val_eq_germ {X : Scheme.{0}} {V : X.Opens} (y : X) (hy : y ∈ V) (a : Γ(X, V)ˣ) :
    (gm (𝟙 X) y V a).val = X.presheaf.germ V y hy a.val := by
  simp only [gm, pullU, dif_pos (show (𝟙 X) y ∈ V from hy)]
  simp
  rfl

private theorem germ_res_val_eq_germ {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (y : X) (hy : y ∈ W)
    (a : Γ(X, V)ˣ) : X.presheaf.germ W y hy (res h a).val = X.presheaf.germ V y (h hy) a.val := by
  simp [res]

theorem isLB_of_chartPull_id {X : Scheme.{0}} {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X))
    (hc : ⨆ i, A.U i = ⊤) : A.IsLB where
  cover := hc
  g_self := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hy' : y ∈ B.U (idx i) := hle i hy
    change X.presheaf.germ (A.U i) y hy (res _ (A.g i i)).val = X.presheaf.germ (A.U i) y hy (1 : Γ(X, A.U i)ˣ).val
    rw [germ_res_val_eq_germ, ← gm_id_val_eq_germ, hg y i i hy hy,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx i) from ⟨hy', hy'⟩),
      ← germ_res_val_eq_germ (le_inf le_rfl le_rfl : B.U (idx i) ≤ _) y hy', hB.g_self (idx i)]
    simp
  cocycle := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i j k
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hi : y ∈ A.U i := hy.1.1
    have hj : y ∈ A.U j := hy.1.2
    have hk : y ∈ A.U k := hy.2
    have hi' : y ∈ B.U (idx i) := hle i hi
    have hj' : y ∈ B.U (idx j) := hle j hj
    have hk' : y ∈ B.U (idx k) := hle k hk
    change X.presheaf.germ _ y hy ((res _ (A.g i j)).val * (res _ (A.g j k)).val) =
      X.presheaf.germ _ y hy (res _ (A.g i k)).val
    rw [map_mul, germ_res_val_eq_germ, germ_res_val_eq_germ, germ_res_val_eq_germ, ← gm_id_val_eq_germ, ← gm_id_val_eq_germ,
      ← gm_id_val_eq_germ, hg y i j hi hj, hg y j k hj hk, hg y i k hi hk,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) from ⟨hi', hj'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx j) ⊓ B.U (idx k) from ⟨hj', hk'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx k) from ⟨hi', hk'⟩)]
    have hB3 := congrArg (fun u : Γ(X, B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k))ˣ =>
      X.presheaf.germ _ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k) from ⟨⟨hi', hj'⟩, hk'⟩) u.val)
      (hB.cocycle (idx i) (idx j) (idx k))
    simp only [Units.val_mul, map_mul, germ_res_val_eq_germ] at hB3
    exact hB3

private theorem gm_id_res_eq {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (y : X) (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 X) y V (res h a) = gm (𝟙 X) y U a := by
  apply Units.ext
  rw [gm_id_val_eq_germ y hy, gm_id_val_eq_germ y (h hy), germ_res_val_eq_germ]

private theorem gs_resG_eq {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (a : Γ(X, U)) : gs f y V (resG X h a) = gs f y U a :=
  gs_res f y h hy a

private theorem mul_eq_unit_mul_of_relations {S : Type _} [CommRing S] (G t t' : Sˣ) (ap aq fp fq sp sq : S)
    (h5 : (t' : S) * t = 1) (E1 : sp = ap * fp) (E2 : sq = aq * fq) (E3 : sp = G * sq) (E4 : fp = t * fq) :
    ap * fp = ((G * t' : Sˣ) : S) * aq * fp := by
  rw [Units.val_mul]
  linear_combination (-1 : S) * E1 + E3 + (G : S) * E2 - ((G : S) * aq * fq) * h5 - ((G : S) * t' * aq) * E4

theorem lbIso_pull_O1_of_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData)
    (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W)
    (hL : L₀.IsLB) (hJ : Generates J σ) (hP : Proportional σ g ψ) (hD : D.idealSheaf = J.comap g) :
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  classical
  have hT : (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL g) (GlobalTheory.CechPic.isLB_dual D.isLB_lb)
  have hGA := generatesAlong_comap_of_generates X W J L₀ m σ g hJ
  rw [← hD] at hGA
  have loc : ∀ (k : L₀.ι) (d : D.ι) (A : W.affineOpens) (hk : A.1 ≤ g ⁻¹ᵁ L₀.U k) (hd : A.1 ≤ D.U d),
      ∃ a c : Fin (m + 1) → Γ(W, A.1), (∀ j, (g.appLE (L₀.U k) A.1 hk).hom ((σ j).f k) =
        a j * resG W hd (D.f d)) ∧ ∑ j, c j * a j = 1 := by
    intro k d A hk hd
    refine exists_quot_of_span_eq (D.regular d A.1 hd) ?_
    rw [← D.ideal_idealSheaf A d hd, hGA.2 k A hk]
  let Idx := {p : L₀.ι × D.ι × W.affineOpens // p.2.2.1 ≤ g ⁻¹ᵁ L₀.U p.1 ∧ p.2.2.1 ≤ D.U p.2.1}
  let tI : Idx → (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).ι := fun p => (fun _ => p.1.1, p.1.2.1)
  have hle : ∀ p : Idx, p.1.2.2.1 ≤ (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).U (tI p) :=
    fun p y hy => ⟨mem_pull.2 (p.2.1 hy), p.2.2 hy⟩
  let N : LB W :=
    { ι := Idx
      U := fun p => p.1.2.2.1
      g := fun p q => res (inf_le_inf (hle p) (hle q))
        ((GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).g (tI p) (tI q)) }
  let cp : ChartPull N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) (𝟙 W) :=
    ⟨tI, hle, fun y p q hp hq => gm_id_res_eq _ y (show y ∈ N.U p ⊓ N.U q from ⟨hp, hq⟩) _⟩
  have hcov : ⨆ p, N.U p = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hgy : g y ∈ ⨆ k, L₀.U k := by rw [hL.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hgy
    obtain ⟨d, hd⟩ := D.exists_mem y
    obtain ⟨A, hyA, hA⟩ := GlobalTheory.EffCartierData.exists_affine_le (X := W)
      (show y ∈ g ⁻¹ᵁ L₀.U k ⊓ D.U d from ⟨hk, hd⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(k, d, A), hA.trans inf_le_left, hA.trans inf_le_right⟩, hyA⟩
  have hN : N.IsLB := isLB_of_chartPull_id hT cp hcov
  have H2 : LBIso N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := GlobalTheory.CechPic.iso_of_chart hT cp
  choose af cf haf hcf using fun p : Idx => loc p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2
  have hcomp : ∀ (j : Fin (m + 1)) (p q : Idx),
      resG W (inf_le_left : N.U p ⊓ N.U q ≤ N.U p) (af p j) =
        (N.g p q : Γ(W, N.U p ⊓ N.U q)) * resG W (inf_le_right : N.U p ⊓ N.U q ≤ N.U q) (af q j) := by
    intro j p q
    have hV : N.U p ⊓ N.U q ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun y hy => ?_)
    have hyp : y ∈ p.1.2.2.1 := hy.1
    have hyq : y ∈ q.1.2.2.1 := hy.2
    rw [gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_resG_eq _ y _ hy,
      gs_resG_eq _ y _ hy, gs_resG_eq _ y _ hy, gs_unit (𝟙 W) y _ hy]
    change _ = (gm (𝟙 W) y _ (res _ _)).val * _ * _
    rw [gm_id_res_eq _ y hy, GlobalTheory.CechPic.gm_tens _ _ _ y _ _ (hle p hyp) (hle q hyq),
      gm_pull_g L₀ g (𝟙 W) y _ _ (hle p hyp).1 (hle q hyq).1]
    have E1 := congrArg (gs (𝟙 W) y (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyp, gs_mul _ _ _ hyp, gs_resG_eq _ _ _ hyp] at E1
    have E2 := congrArg (gs (𝟙 W) y (N.U q)) (haf q j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyq, gs_mul _ _ _ hyq, gs_resG_eq _ _ _ hyq] at E2
    have hk2 : (𝟙 W ≫ g) y ∈ L₀.U p.1.1 ⊓ L₀.U q.1.1 := ⟨p.2.1 hyp, q.2.1 hyq⟩
    have E3 := congrArg (gs (𝟙 W ≫ g) y (L₀.U p.1.1 ⊓ L₀.U q.1.1)) ((σ j).compat p.1.1 q.1.1)
    rw [gs_res _ _ _ hk2, gs_mul _ _ _ hk2, gs_unit _ _ _ hk2, gs_res _ _ _ hk2] at E3
    have hd2 : (𝟙 W) y ∈ D.U p.1.2.1 ⊓ D.U q.1.2.1 := ⟨p.2.2 hyp, q.2.2 hyq⟩
    have E4 := congrArg (gs (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1)) (D.trans_spec p.1.2.1 q.1.2.1)
    rw [gs_resG_eq _ _ _ hd2, gs_mul _ _ _ hd2, gs_unit _ _ _ hd2, gs_resG_eq _ _ _ hd2] at E4
    have E5 : ((gm (𝟙 W) y ((GlobalTheory.CechPic.dual D.lb).U (tI p).2 ⊓ (GlobalTheory.CechPic.dual D.lb).U (tI q).2))
        ((GlobalTheory.CechPic.dual D.lb).g (tI p).2 (tI q).2)).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1 := by
      change (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)⁻¹).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    exact mul_eq_unit_mul_of_relations _ _ _ _ _ _ _ _ _ E5 E1 E2 E3 E4
  let t : Fin (m + 1) → N.Sec := fun j => { f := fun p => af p j, compat := fun p q => hcomp j p q }
  have ht : ⨆ i, Out.nonzeroLocus (t i) = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hcf p) hyp
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, GlobalTheory.basicOpen_le_nonzeroLocus (t j) p hj⟩
  have hch : ∀ y : W, ∃ i, y ∈ ψ ⁻¹ᵁ chart R m i := by
    intro y
    have h := iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ
    have hy : y ∈ ⨆ i, Out.nonzeroLocus (secPull (coord R m i) ψ) := by rw [h]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    have e := toProj_preimage_chart (ψ ≫ PSpace.str R m) (fun i => secPull (coord R m i) ψ)
      (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ) i
    rw [toProj_secPull_coord] at e
    rw [e]
    exact hi
  have hψ : ψ = toProj (ψ ≫ PSpace.str R m) t ht := by
    refine eq_toProj_of_locally (s := t) ht rfl (fun y => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨i, hi⟩ := hch y
    refine ⟨N.U p ⊓ ψ ⁻¹ᵁ chart R m i, ⟨hyp, hi⟩, p, inf_le_left, i, inf_le_right,
      resG W inf_le_left (af p i), fun j => ?_⟩
    have hV : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    have hk' : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ g ⁻¹ᵁ L₀.U p.1.1 := inf_le_left.trans p.2.1
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun z hz => ?_)
    have hzp : z ∈ N.U p := hz.1
    have Ej := congrArg (gs (𝟙 W) z (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ej
    have Ei := congrArg (gs (𝟙 W) z (N.U p)) (haf p i)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ei
    have Eh := congrArg (gs (𝟙 W) z _) (hP _ p.1.1 hk' i inf_le_right j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hz, gs_mul _ _ _ hz, gs_appLE g _ _ _ (𝟙 W) z hz] at Eh
    rw [gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_resG_eq _ _ _ hz, gs_resG_eq _ _ _ hz,
      gs_resG_eq _ _ _ hz]
    linear_combination (-1 : W.presheaf.stalk z) * Ej + Eh + gs (𝟙 W) z _ (pullRatio ψ _ i inf_le_right j) * Ei
  have H1 : LBIso ((O1 R m).pull ψ) N := by
    have h := lbIso_pullback_O1_toProj (ψ ≫ PSpace.str R m) t ht
    rw [← hψ] at h
    exact h
  exact LBIso.trans (pull_isLB (O1_isLB R m) ψ) hN hT H1 H2

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnLevelAtTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_mul_on_level_at_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  first | exact @GlobalTheory.TwistRowMul.lamRow_mul | exact GlobalTheory.TwistRowMul.lamRow_mul | (intros; apply GlobalTheory.TwistRowMul.lamRow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_mul_on_symmetricLevel_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → P ∈ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) true j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) true j P, lamRow Ch mu true j P (g * g').toLinearMap = lamRow Ch mu true j P g.toLinearMap * lamRow Ch mu true j P g'.toLinearMap := by
  first | exact @GlobalTheory.SymLevelMul.lamRow_mul | exact GlobalTheory.SymLevelMul.lamRow_mul | (intros; apply GlobalTheory.SymLevelMul.lamRow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_one_add_prime_smul_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | exact GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | (intros; apply GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwistedStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted : ∀ (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X), Generates J σ → GeneratesAlong (J.comap g) σ g := by
  first | exact @GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | exact GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | (intros; apply GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCompletelyOverIntermediateOfSplitsOverRatStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  first | exact @GlobalTheory.SplitTower.splits_completely_of_intermediate | exact GlobalTheory.SplitTower.splits_completely_of_intermediate | (intros; apply GlobalTheory.SplitTower.splits_completely_of_intermediate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.OrientedSmall

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace_oriented (P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a = (P * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a
      = ∑ e, ∑ b, ∑ d, P a b * c (y e b) * K e d * x d a := Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ b, P a b * c (y e b) * K e d * x d a := Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem trace_coord (J P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hP : P.map c = Pᵀ) (x y : Matrix (Fin m) (Fin n) R) :
    (P * (y.map c)ᵀ * K * x).trace = ((((y * P)ᵀ).map c)ᵀ * Jᵀ * (x * P)ᵀ * Kᵀ).trace := by
  have e1 : Jᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPJ, Matrix.transpose_one]
  rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_mul, hP, Matrix.transpose_mul]
  calc (P * (y.map c)ᵀ * K * x).trace
      = (P * (y.map c)ᵀ * (K * x)).trace := by simp only [Matrix.mul_assoc]
    _ = (K * x * (P * (y.map c)ᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (K * x * (P * (y.map c)ᵀ))ᵀ.trace := (Matrix.trace_transpose _).symm
    _ = (y.map c * Pᵀ * xᵀ * Kᵀ).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (y.map c * Pᵀ * (Jᵀ * Pᵀ) * xᵀ * Kᵀ).trace := by rw [e1, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem act_coord (J P g g' : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hg : (g.map c)ᵀ * J * g = J) (hgg : g * g' = 1) (x : Matrix (Fin m) (Fin n) R) :
    (h * x * g' * P)ᵀ = g.map c * (x * P)ᵀ * hᵀ := by
  have hJP : J * P = 1 := mul_eq_one_comm.1 hPJ
  have key : g' * P = P * (g.map c)ᵀ := by
    calc g' * P = (P * J) * g' * P := by rw [hPJ, Matrix.one_mul]
      _ = P * ((g.map c)ᵀ * J * g) * g' * P := by rw [hg]
      _ = P * (g.map c)ᵀ * (J * ((g * g') * P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgg, Matrix.one_mul, hJP, Matrix.mul_one]
  rw [Matrix.mul_assoc (h * x), key]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Generic

variable {D : D7}

theorem cA_incA (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, incA, inclR, CMData.sig, starRingEnd_apply]

theorem gram_conjTranspose (V : HSp D) : V.gramᴴ = V.gram := by
  refine Matrix.ext fun i j => ?_
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gramInv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gramInv_map (V : HSp D) :
    ((V.gram⁻¹).map (incA D)).map (cA D) = ((V.gram⁻¹).map (incA D))ᵀ := by
  have h : (V.gram⁻¹)ᴴ = V.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_conjTranspose]
  ext i j
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [cA_incA, this]

theorem mt_mul_inv (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem hO_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    hO S T x y = hHom S T (toTWsmall S T y) (toTWsmall S T x) := by
  unfold hO hHom
  rw [if_pos hr]
  have s := sum_eq_trace (cA D) (S.gram.map (incA D)) (T.gram.map (incA D))
    (toTWsmall S T y) (toTWsmall S T x)
  have s' := sum_eq_trace_oriented (cA D) ((S.gram⁻¹).map (incA D)) (T.gram.map (incA D)) x y
  simp only [Matrix.map_apply] at s s'
  rw [s, s']
  exact trace_coord (cA D) _ _ _ (gramInv_mul S) (gramInv_map S) x y

theorem bridgeSmall (D : D7) : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · unfold symplO sympl
    rw [hO_eq S T hr]
  · unfold actHom
    rw [if_pos hr]
    exact act_coord (cA D) _ _ _ _ _ (gramInv_mul S) (mt_rel S g) (mt_mul_inv S g) x

end GlobalTheory.OrientedSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem char_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ P O _ _ _ _ _ hO χ hχ hm hmP hk σ σ' u u' hσ hσ' huu
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A P := exists_isPlaceOver Ω P
  obtain ⟨ρ, hs, ϖ, π, hϖ, hϖ2, hπ, hv⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ u hσ
  obtain ⟨ρ', hs', ϖ', π', hϖ', hϖ2', hπ', hv'⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ' u' hσ'
  have hconj : ∀ a b : G E Ω, χ (a⁻¹ * b * a) = χ b := by
    intro a b
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  rw [← hconj ρ σ, ← hconj ρ' σ']
  set s := ρ⁻¹ * σ * ρ
  set s' := ρ'⁻¹ * σ' * ρ'
  set m := normV P - 1
  rw [zpow_one] at hv hv'
  rw [← GlobalTheory.TameTau.tame_quot_indep A P hA m hm hmP ϖ ϖ' hϖ hϖ2 hϖ' hϖ2' π π' hπ hπ' s' hs'] at hv'
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Submodule.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  have hroot : ∀ t : G E Ω, (t π / π) ^ m = 1 := by
    intro t
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  have hlt : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P.asIdeal := by
    intro x
    exact hA x
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hlt]
    simpa using h
  have hu : A.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
    have := (hlt (u - u')).2 huu
    simpa using this
  have heq : s π / π = s' π / π := by
    refine root_eq_of_close A m (hroot s) (hroot s') hmv ?_
    have e : s π / π - s' π / π = (s π / π - algebraMap E Ω (u : E))
        + (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) - (s' π / π - algebraMap E Ω (u' : E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ (Valuation.map_add_lt _ hv hu) hv'
  exact GlobalTheory.T.continuous_char_eq_of_inertia_condition A P hA hO χ hχ m hm hmP (hk A hA) ϖ hϖ hϖ2 π hπ s hs s' hs'
    ((div_left_inj' hπ0).1 heq)

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharArg_mul_left_unipotent : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  first | exact @GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | exact GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | (intros; apply GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbeddingStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  first | exact @GlobalTheory.Mem.LatGood.lawGood | exact GlobalTheory.Mem.LatGood.lawGood | (intros; apply GlobalTheory.Mem.LatGood.lawGood <;> assumption)
end

