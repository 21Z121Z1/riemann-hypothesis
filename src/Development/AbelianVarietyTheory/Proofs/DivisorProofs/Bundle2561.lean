import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  first | exact @GlobalTheory.Proof.abelianDeRhamFree_of_hodge | exact GlobalTheory.Proof.abelianDeRhamFree_of_hodge | (intros; apply GlobalTheory.Proof.abelianDeRhamFree_of_hodge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeDual

theorem lam_mul_left (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a a' t : T ⟶ A) :
    lam (cls L hL) (a * a') t = lam (cls L hL) a t + lam (cls L hL) a' t := by
  have h := hC S A hA L hL T a a' t
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![a * a' * t, a * a', a * t, a' * t, a, a', t, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  unfold lam
  rw [← sub_eq_zero, ← e]
  abel

theorem evc_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem isAdditive_lam (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) : IsAdditive (abelian₂ A L) ∧ IsAdditive (swap (abelian₂ A L)) := by
  haveI := hA.comm
  have hs : (swap (abelian₂ A L)).IsLB := pull_isLB hP _
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_iff hs).2 fun Y a a' t ↦ ?_⟩
  · rw [evc_lam hL, evc_lam hL, evc_lam hL]
    exact lam_mul_left hC hA hL a a' t
  · rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_lam hL, evc_lam hL, evc_lam hL, lam_comm, lam_comm _ t a,
      lam_comm _ t a']
    exact lam_mul_left hC hA hL a a' t

theorem mono_of_isPerfect' {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) [IsMonHom x] : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem abelianDeRham_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  intro hC hD hPD hF R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨haddL, haddS⟩ := isAdditive_lam hC hA hL hP
  obtain ⟨B, _, P, hB, hdim, h1, h2⟩ := hD (Sp R) A hA
  have hgB := hdim g hg
  obtain ⟨x, hx, -⟩ := h1.univ A (abelian₂ A L) hP haddL
  haveI hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying (Sp R) A A B (abelian₂ A L) P h1 h2.additive hP haddS x hx
  have perf := h1.isPerfect h2
  obtain ⟨φ, hφ⟩ := exists_isCorrForm (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hgB))
    perf.isLB perf.zero_left perf.zero_right
  have e : LBIso (P.pull (lift (fst A A) (snd A A ≫ x)).left) (abelian₂ A L) :=
    (cls_eq_iff (pull_isLB h1.isLB _) hP).1 ((cls_eq_iff hP (pull_isLB h1.isLB _)).2 hx).symm
  obtain ⟨φ', hφ', k⟩ := hφ.pull h1.isLB (homMor (dp0 R) (𝟙 _) (𝟙 A)) (homMor (dp0 R) (𝟙 _) x)
    (h := (lift (fst A A) (snd A A ≫ x)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd])
    hP e
  have hψ' := isCorrForm_lam hψ
  obtain rfl := hφ'.unique (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)) hP hψ'
  have hform : ∀ a b, φ' a b = φ a (push (dp0 R) (𝟙 _) x b) := fun a b ↦ by
    have := k (push (dp0 R) (𝟙 _) (𝟙 A) a) a (push (dp0 R) (𝟙 _) x b) b (fun _ ↦ rfl) fun _ ↦ rfl
    rw [this, push_id]
    rfl
  obtain ⟨-, orth⟩ := hPD R A B g hA hB hg hgB P h1 φ hφ
  refine ⟨fun a ha b hb ↦ ?_, fun hK ↦ ?_⟩
  · rw [hform]
    exact orth a ha _ (push_mem_Fil x hb)
  · have mx : Mono x := mono_of_isPerfect' h1 (isPerfect_lam hL hK) x hx
    have ix : IsIso x := GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension (Sp R) A B hA hB g hg hgB x hmx mx
    have hd : IsDual A A (abelian₂ A L) := GlobalTheory.AbDual.transport (Sp R) A A B (abelian₂ A L) P h1 hP x ix hmx hx
    exact (hPD R A A g hA hA hg hg (abelian₂ A L) hd φ' hψ').1

end GlobalTheory.CubeDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfHyp
section
namespace GlobalTheory

theorem abelianDualCrystal_of_dual_of_smoothLift :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianDualCrystal :=
  fun h₁ h₂ => ⟨h₁, GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison h₂⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelow
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt

namespace GlobalTheory.AmpleHtLow

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem small_of_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ), 1 ≤ m → ∀ (s : (L.pow m).B.Sec), ∃ c : ℝ,
      s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec := by
  intro k _ X p D hX L m hm s
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range (((L.pow m).cInf σ).continuous_nsq s)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  have hK' : ∀ σ, K σ ≤ ∑ τ, |K τ| + 1 := fun σ => by
    have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]
  have h1 : (1 : ℝ) ≤ ∑ τ, |K τ| + 1 := by
    linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  set K' : ℝ := ∑ τ, |K τ| + 1
  have hl : 0 ≤ Real.log K' := Real.log_nonneg h1
  have hpos : 0 < K' := by linarith
  refine ⟨-(Real.log K' / 2), fun σ y => ?_⟩
  refine (le_of_eq (nsq_shift_pow L (fun _ => -(-(Real.log K' / 2))) (fun _ => rfl) m σ (CxPts.secVal p σ s) y)).trans ?_
  have h0 : 0 ≤ ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y := by unfold Weight.nsq; positivity
  have h2 : Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2)))) ≤ K'⁻¹ := by
    rw [show -(2 * (m : ℝ) * -(-(Real.log K' / 2))) = -((m : ℝ) * Real.log K') by ring,
      ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_log hpos]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y * Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2))))
      ≤ K' * K'⁻¹ := mul_le_mul ((hK σ y).trans (hK' σ)) h2 (Real.exp_pos _).le hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem htLow (hE : GlobalTheory.Published.ArExists) (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (hI : A.Induced M L q 0) (hA : Y.ample A.D) :
    ∃ C : ℝ, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → -C ≤ A.ht x := by
  have := M.ar.isIntegral
  obtain ⟨m, hm, N, t, ht⟩ := GlobalTheory.T.power_of_induced_bundle_generated F (cxSt F) Y A M L q 0 hI hA
  have hs : ∀ i, ∃ s : (L.pow m).B.Sec, ∀ y : Y.X,
      M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t i) :=
    fun i => GlobalTheory.T.nonzero_locus_section_pullback_extends F Y M _ (L.pow m).isLB (t i)
  choose s hs using hs
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => small_of_shift (𝓞 F) M.X M.p Y.dim M.ar L m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hE _ M.X M.p _ M.ar).1 L
  have hk : (0 : ℝ) < ((q : ℕ) : ℝ) * (A.n : ℕ) := mul_pos (Nat.cast_pos.2 q.pos) (Nat.cast_pos.2 A.n.pos)
  refine ⟨(∑ i, |c i|) / (((q : ℕ) : ℝ) * (A.n : ℕ)), fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t i) :=
    TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ x))
  have hN : (0 : ℝ) < Nat.card (M.X.residueField (M.j x) →+* ℂ) :=
    Nat.cast_pos.2 (NefModel.card_pos M hx)
  have hb : IsPtHt L (M.j x) (h (M.j x) / Nat.card (M.X.residueField (M.j x) →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt (𝓞 F) M.X M.p Y.dim M.ar L m (c i) _ (M.j x) (s i) hm (hc i)
    ((hs i x).2 hi) (ClosedAlg.isAlgPt_of_isClosed F Y M x hx) hb
  rw [HtModel.ht_eq F _ Y A M L q hI x _ hx hb]
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  rw [← neg_div]
  exact div_le_div_of_nonneg_right (h2.trans h1) hk.le

theorem main : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp, ∃ C : ℝ,
    ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → -C ≤ (O.met.ab c).ht b := by
  intro hP _ D O hO c
  obtain ⟨x, P, h⟩ := hO
  obtain ⟨M, L, q, hI, -⟩ := P.ab_model c
  rw [h.ab_eq]
  exact htLow hP.p4.arExists _ _ _ M L q hI (P.ab_ample c)

end GlobalTheory.AmpleHtLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftDeRhamUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OActLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in

theorem _root_.GlobalTheory.OActLift.isMonHom_mul_of_comm {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem exists_oAct_lift : GlobalTheory.Published.GrothendieckDeformation → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I),
    IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
      (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (O : Type) [CommRing O] (a₀ : OAct O A₀), (∀ (x : O), ∀ d ∈ liftFil κ h, act κ (spMap π) a₀ x d ∈ liftFil κ h) →
      ∃ a : OAct O A, ∀ x, (a₀.act x).left ≫ i = i ≫ (a.act x).left := by
  intro GD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg O _ a₀ hfil
  have HL := (GD R I κ hκ R₀ π hπ hI).2.2
  haveI : IsCommMonObj A := hA.comm
  have key : ∀ x : O, ∃! f : A ⟶ A, IsMonHom f ∧ i ≫ f.left = (a₀.act x).left ≫ i := fun x ↦ by
    haveI := a₀.hom x
    exact HL g A₀ A i h hA hg g A₀ A i h hA hg (a₀.act x) (fun d hd ↦ hfil x d hd)
  choose f hf huniq using key
  refine ⟨⟨f, fun x ↦ (hf x).1, ?_, ?_, ?_⟩, fun x ↦ (hf x).2.symm⟩
  · refine (huniq 1 (𝟙 _) ⟨inferInstance, ?_⟩).symm
    rw [a₀.one]
    simp
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x * y) (f x ≫ f y) ⟨inferInstance, ?_⟩).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, ← Category.assoc, (hf x).2, Category.assoc, (hf y).2,
      Category.assoc]
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x + y) (f x * f y) ⟨isMonHom_mul_of_comm _ _, ?_⟩).symm
    rw [a₀.add]
    let j : Over.mk (A₀.hom ≫ spMap π) ⟶ A := Over.homMk i h.1.w
    have e := h.2 A₀ (a₀.act x) (a₀.act y) (j ≫ f x) (j ≫ f y) (hf x).2 (hf y).2
    rw [← MonObj.comp_mul] at e
    exact e

end GlobalTheory.OActLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFacts
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem abelianLift_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  have F : AbelianDeRham.Free :=
    GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.Proof.abelianDeRhamFree_of_hodge H1 H2)
  have C : CrystallineDeRham := H1.toCrystallineDeRham
  have Rg : AbelianDeRham.Rigid := AbelianDeRham.rigid_of_free_of_crystallineDeRham F C
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h'.1 hg
  have p' : AllPrim (dp0 R) (𝟙 _) A' := (F R A' g hA hg).1
  have p₀ : AllPrim (dp0 R₀) (𝟙 _) A₀ := (F R₀ A₀ g hA₀ hg₀).1
  have hκ : IsNilDP (divided₂ hI) := isDPNilpotent_squareZero hI
  have bij := Rg R A' g hA hg I (divided₂ hI) hκ R₀ π hπ hk A₀ i' h'
  have := hA.smooth
  have := hA.proper
  obtain ⟨b₁, -⟩ := C R I (divided₂ hI) hκ R₀ π hπ hk A'.left A₀.left (A'.hom ≫ 𝟙 _) A₀.hom i' inferInstance
    inferInstance inferInstance (by rw [Category.comp_id]; exact h'.1) (liftMor (divided₂ hI) h').isMor
  have pc : AllPrim (divided₂ hI) (spMap π) A₀ := by
    refine Submodule.eq_top_iff'.2 fun c ↦ ?_
    obtain ⟨c', rfl⟩ := b₁.2 c
    have hc' : c' ∈ prim (dp0 R) (𝟙 _) A' := by rw [show prim (dp0 R) (𝟙 _) A' = ⊤ from p']; trivial
    exact (liftMor (divided₂ hI) h').pullback_mem_primitive hc'
  let e := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').isMor.pull1 b₁
  have fin : Module.Finite R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.1
  have proj : Module.Projective R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.2.1
  exact ⟨p', p₀, pc, bij, Module.Finite.equiv e, Module.Projective.of_equiv e, hA₀, hg₀⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfDeRhamUnobstructed
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem NilExp.mono {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {N M : ℕ} (h : NilExp κ N)
    (e : N ≤ M) : NilExp κ M :=
  fun l hl hs ↦ h l hl (e.trans hs)

theorem NilExp.eq_zero {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) {a : R}
    (ha : a ∈ I) : a = 0 := by

  have h1 := h [(1, a)] (by simpa using ha) (by simp)
  simpa [κ.dpow_one ha] using h1

theorem NilExp.eq_sqDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) :
    ∃ hI : I ^ 2 = 0, κ = divided₂ hI := by
  have hbot : I = ⊥ := eq_bot_iff.2 fun a ha ↦ (Ideal.mem_bot).2 (h.eq_zero ha)
  have hI : I ^ 2 = 0 := by
    rw [hbot, pow_two, Ideal.mul_bot]
    rfl
  refine ⟨hI, ?_⟩

  ext n x hx
  obtain rfl := h.eq_zero hx
  rcases n with _ | _ | n
  · rw [κ.dpow_zero hx, (divided₂ hI).dpow_zero hx]
  · rw [κ.dpow_one hx, (divided₂ hI).dpow_one hx]
  · rw [squareZeroDividedPowers_dpow hI (by omega), κ.dpow_eval_zero (by omega)]

theorem abelianLifting_of_sqLifting (hD : AbelianDeRham) (hU : AbelianUnobstructed) (hS : SqLifting) :
    AbelianLifting := by

  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → NilExp κ (n + 1) →
        LiftObj κ π ∧ LiftHom κ π := by
    intro n
    induction n with
    | zero =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨hI, rfl⟩ := NilExp.eq_sqDP h
      exact hS R I hI R₀ π hπ hker
    | succ n ih =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨R₁, _, J, hJ, ρ, I₁, κ₁, π₁, st, h₁⟩ := exists_isStep_nilExp R R₀ I κ π hπ hker n h
      have hsq := hS R J hJ R₁ ρ st.surj st.kerJ
      have hih := ih R₁ I₁ κ₁ R₀ π₁ st.surj₁ st.ker₁ h₁
      exact ⟨GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization hD hU R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.1 hih.1,
        liftHom_of_isStep hD R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.2 hih.2⟩
  intro R _ I κ hκ R₀ _ π hπ hker
  obtain ⟨N, hN⟩ := (isPDNilpotent_iff κ).1 hκ
  exact key N R I κ R₀ π hπ hker (hN.mono (Nat.le_succ N))

theorem abelianLifting_of_schemeLifts :
    AbelianDeRham → AbelianSchemeLifts → AbelianUnobstructed → AbelianLifting := by
  intro hD hL hU
  refine abelianLifting_of_sqLifting hD hU (GlobalTheory.T.squareZeroLifting_of_noetherian_case hD ?_)
  intro R _ _ I hI R₀ _ π hπ hk
  exact ⟨GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk),
    GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk)⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentWithUniformizationStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_descent_with_uniformization : ∀ (k : Type) [Field k] (σ : k →+* ℂ) (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A]
    (p : A.left ⟶ A₀.left) (L : LB A.left) (u : HolUnif A L 1), IsAbelianScheme A₀ → SmoothOfRelativeDimension 1 A₀.hom →
    IsGrpPullback A A₀ (spMap σ) p → L.IsLB → ∀ n : ℕ,
  ∃ (B₀ : Over (Sp k)) (_ : GrpObj B₀) (B : Over (Sp ℂ)) (_ : GrpObj B) (q : B.left ⟶ B₀.left) (M : LB B.left)
    (v : HolUnif B M n), IsAbelianScheme B₀ ∧ SmoothOfRelativeDimension n B₀.hom ∧ IsAbelianScheme B ∧
    SmoothOfRelativeDimension n B.hom ∧ IsGrpPullback B B₀ (spMap σ) q ∧ ∀ z ∈ v.Λ, ∀ j, (fun _ : Fin 1 ↦ z j) ∈ u.Λ := by
  first | exact @GlobalTheory.EllPowModel.main | exact GlobalTheory.EllPowModel.main | (intros; apply GlobalTheory.EllPowModel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfKerLeOfNilpotentReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QuotEq

theorem eq_of_ker_le_of_reduction : ∀ (A κ : Type) [CommRing A] [CommRing κ] (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (G B : Over (Sp A)) [GrpObj G] [GrpObj B], IsAbelianScheme B → ∀ (q₁ q₂ : G ⟶ B), IsMonHom q₁ → IsMonHom q₂ → Flat q₁.left → Surjective q₁.left → QuasiCompact q₁.left → (∀ (T : Over (Sp A)) (x : T ⟶ G), x ≫ q₁ = 1 → x ≫ q₂ = 1) → pullback.fst G.hom (spMap π) ≫ q₁.left = pullback.fst G.hom (spMap π) ≫ q₂.left → q₁ = q₂ := by
  intro A κ _ _ π hπ hnil G B _ _ hB q₁ q₂ h₁ h₂ hfl hsu hqc hker hκ
  haveI := h₁; haveI := h₂; haveI := hfl; haveI := hsu; haveI := hqc
  obtain ⟨d, hd⟩ := GlobalTheory.ExtensionRigidity.exists_factor q₁ q₂ (fun W a b h => by
    have e : (a * b⁻¹) ≫ q₁ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]
    have e₂ := hker W (a * b⁻¹) e
    rw [MonObj.mul_comp, GrpObj.inv_comp] at e₂
    exact mul_inv_eq_one.1 e₂)
  have hη : η[B] ≫ d = η[B] := by
    calc η[B] ≫ d = (η[G] ≫ q₁) ≫ d := by rw [IsMonHom.one_hom q₁]
      _ = η[B] := by rw [Category.assoc, hd, IsMonHom.one_hom q₂]
  haveI hdm : IsMonHom d := GlobalTheory.rigidity_holds (Sp A) B B hB hB d hη
  let qκ : pullback G.hom (spMap π) ⟶ pullback B.hom (spMap π) :=
    pullback.lift (pullback.fst G.hom (spMap π) ≫ q₁.left) (pullback.snd G.hom (spMap π))
      (by rw [Category.assoc, Over.w, pullback.condition])
  have hq₁ : qκ ≫ pullback.fst B.hom (spMap π) = pullback.fst G.hom (spMap π) ≫ q₁.left :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback (pullback.fst G.hom (spMap π)) qκ q₁.left (pullback.fst B.hom (spMap π)) := by
    refine IsPullback.of_bot ?_ hq₁.symm (IsPullback.of_hasPullback B.hom (spMap π))
    rw [pullback.lift_snd, Over.w]
    exact IsPullback.of_hasPullback G.hom (spMap π)
  haveI : Flat qκ := MorphismProperty.of_isPullback hsq hfl
  haveI : Surjective qκ := MorphismProperty.of_isPullback hsq hsu
  haveI : QuasiCompact qκ := MorphismProperty.of_isPullback hsq hqc
  have hfib : pullback.fst B.hom (spMap π) ≫ d.left = pullback.fst B.hom (spMap π) := by
    rw [← cancel_epi qκ, reassoc_of% hq₁, ← Over.comp_left, hd, ← hκ, hq₁]
  have hP := isGrpPullback_pullback B (spMap π)
  have hu := GlobalTheory.HomLift.existsUnique_isMonHom_lift A κ π hπ hnil _ _ B B _ _ hP hP hB hB
    (𝟙 ((Over.pullback (spMap π)).obj B)) (𝟙 B) (by simp)
  have hd1 : d = 𝟙 B := hu.unique ⟨hdm, by simpa using hfib⟩ ⟨inferInstance, by simp⟩
  rw [← hd, hd1, Category.comp_id]

end GlobalTheory.Mum.QuotEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyChartAffineOfChartFiniteTypeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFamily_chart_affine_of_chart_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → (∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  first | exact @GlobalTheory.DualApprox.chartAt_of_finiteType | exact GlobalTheory.DualApprox.chartAt_of_finiteType | (intros; apply GlobalTheory.DualApprox.chartAt_of_finiteType <;> assumption)
end

