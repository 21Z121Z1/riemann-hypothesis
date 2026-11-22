import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRank
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem exists_mem_cellOpen (ι : Type) [Fintype ι] (N : ℕ) (y : Fl ι N) :
    ∃ w : ι → Equiv.Perm (Fin N), y ∈ cellOpen ι N w := by
  obtain ⟨w, hw⟩ := GlobalTheory.FlagZ.exists_mem_range_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd y
  exact ⟨w, (mem_cellOpen ι N).2 hw⟩

theorem mem_sub_iff_cellCol (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (w : ι → Equiv.Perm (Fin N))
    (V : (Fl ι N).Opens) (h : V ≤ cellOpen ι N w) (a : Fin N → Γ(Fl ι N, V)) :
    (∑ j, a j • resM _ h (cellCol ι N w τ j)) ∈ (sub ι N τ l).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 :=
  GlobalTheory.T.subbundle_frame_membership _ (GlobalTheory.T.cell_columns_frame ι N w τ) _ _
    (fun y hy => (GlobalTheory.T.flag_stalk_column_span ι N τ l y _ (GlobalTheory.T.cell_flag_point_stalk ι N w y hy)).trans (GlobalTheory.T.cell_flag_stalk_span ι N w τ l y hy)) h a

theorem isVB_F_and_isSubbundle_incl : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (i : Fin (N + 1)),
    VB.IsVB (F ι N τ i) i ∧ VB.IsSubbundle (incl ι N τ i) := by
  intro ι _ N τ i
  refine ⟨fun y => ?_, ⟨?_, N - i, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_mem_cellOpen ι N y
    obtain ⟨e, he⟩ := GlobalTheory.T.subbundle_frame_exists (sub ι N τ i) _ (GlobalTheory.T.cell_columns_frame ι N w τ) i i.is_le
      (mem_sub_iff_cellCol ι N τ i w)
    exact ⟨_, e, hw, he⟩
  · exact @mono_comp _ _ _ _ _ _ (VB.Sub.mono_incl _) _ inferInstance
  · refine (show VB.IsVB (cokernel (sub ι N τ i).incl) (N - i) from fun y => ?_).of_iso
      (cokernelCompIsIso _ _).symm
    obtain ⟨w, hw⟩ := exists_mem_cellOpen ι N y
    obtain ⟨e, he⟩ := GlobalTheory.T.quotient_bundle_frame_exists (sub ι N τ i) _ (GlobalTheory.T.cell_columns_frame ι N w τ) i i.is_le
      (mem_sub_iff_cellCol ι N τ i w)
    exact ⟨_, e, hw, he⟩

end GlobalTheory.FlagZ.Univ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

open GlobalTheory.TensAct

section Main

theorem mside : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  intro R _ _ I D D' r W T A f hf hW
  classical
  let M : Fin 4 → Matrix (Fin r) (Fin r) ℤ := ![1 + A, 1, A, 0]
  let e : Fin 4 → ℤ := ![1, -2, -1, 2]
  let E : Fin 4 × (Fin r × Fin r) → ℤ := fun q => e q.1 * W q.2.1 q.2.2
  have hB := fun q : Fin 4 × (Fin r × Fin r) => GlobalTheory.T.mumfordLambda_bilinear_integral_combinations R I D D'.P.A T.pr (M q.1 q.2.1) (M q.1 q.2.2)
  choose t ht hv using hB
  have hP := fun q : Fin 4 × (Fin r × Fin r) => exists_zpow D.toPre.P.isLB (t q) (ht q) (E q)
  choose s hs hsv using hP
  have hpr : ∀ (a : Fin 4) (i : Fin r), GlobalTheory.TensAct.matAct T (M a) ≫ T.pr i = ∏ k, T.pr k ^ M a i k :=
    fun a i => GlobalTheory.TensAct.matAct_pr T (M a) i
  obtain ⟨t', ht', hv'⟩ := exists_gen D.toPre.P.isLB
    (φ' := fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2)
    (ε' := fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) (by
      intro U _ h
      let Lh : (D'.P.A ⟶ D.toPre.P.A) → (D'.P.A ⟶ D.toPre.P.A) → U :=
        fun x x' => ∏ l : Fin 4, h (GlobalTheory.PolDeg.lamPts x x' l) ^ Oε l
      let P : Fin 4 → Fin r → (D'.P.A ⟶ D.toPre.P.A) := fun a i => ∏ k, T.pr k ^ M a i k
      have lamS : ∀ k l, Lh (T.pr k) (T.pr l) = Lh (T.pr l) (T.pr k) := by
        intro k l
        simp only [Lh, Fin.prod_univ_four]
        show h (T.pr k * T.pr l).left ^ (1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) =
          h (T.pr l * T.pr k).left ^ (1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ)
        rw [mul_comm (T.pr k) (T.pr l)]
        ac_rfl
      have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one U W A (fun k l => Lh (T.pr k) (T.pr l)) lamS hW
      have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
          (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
        rw [Fintype.prod_prod_type]
        exact Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
      have hR : ∏ p : Fin 4 × ((Fin r × Fin r) × Fin 4), h ((![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
          (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) ^
          ((![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) =
          ∏ q : Fin 4 × (Fin r × Fin r), Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q := by
        rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun ij _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [four_eq T A f hf a, comp_tensφ', hpr, hpr, ← zpow_mul]
        congr 1
        simp only [tensε, E, e]
        ring
      have hL : ∀ q : Fin 4 × (Fin r × Fin r), ∏ κ : Fin 4 ⊕ ((Fin r × Fin r) × Fin 4),
          h (Sum.elim (GlobalTheory.PolDeg.lamPts (P q.1 q.2.1) (P q.1 q.2.2))
            (fun m : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (T.pr m.1.1) (T.pr m.1.2) m.2) κ) ^
          (E q * Sum.elim Oε (fun m : (Fin r × Fin r) × Fin 4 => -(M q.1 q.2.1 m.1.1 * M q.1 q.2.2 m.1.2 * Oε m.2)) κ) =
          Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q * ((∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
            (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q)⁻¹ := by
        intro q
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        congr 1
        · rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, mul_comm]
        · rw [← zpow_neg, ← Finset.prod_zpow, Fintype.prod_prod_type, Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, ← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l' _ => ?_
          rw [← zpow_mul]
          congr 1
          ring
      rw [hR, Fintype.prod_prod_type]
      refine (Finset.prod_congr rfl fun q _ => hL q).trans ?_
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, H2, inv_one, _root_.mul_one]) (GeneratorPullback.finProdGen D.toPre.P.L _ _ s)
    (finProd_isGen _ _ s hs)
  refine ⟨t', ht', fun y z J hJ => ?_⟩
  let ρ : TK R ⟶ D'.P.A := toUnit (TK R) ≫ D'.c y
  have hρ : ∀ k, ρ ≫ T.pr k = toUnit (TK R) ≫ D.toPre.c (T.xe y k) := fun k => by
    rw [Category.assoc, T.c_pr]
  have lamS : ∀ k l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J =
      val (D.toPre.tau (T.xe y l) (T.xe y k)) (𝟙 _) z J := fun k l => DVR.tauK_symm hJ _ _
  have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one _ W A _ lamS hW
  have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^
      (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
    rw [Fintype.prod_prod_type]
    refine Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
  have hq : ∀ q : Fin 4 × (Fin r × Fin r), val (s q) (D'.xK y) z J =
      ((val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.1) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.2)) (𝟙 _) z J)⁻¹ *
        ∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q := fun q => by
    rw [hsv q _ _ z J hJ, show D'.xK y = ρ.left from rfl, hv q ρ (fun k => T.xe y k) hρ z J hJ, xe_four, xe_four]
  rw [hv' _ _ z J hJ, val_finProd _ _ _ _ _ hJ, Finset.prod_congr rfl fun q _ => hq q]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [H2, _root_.mul_one, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  simp only [E, e]
  ring

end Main

end GlobalTheory.MumSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
open GlobalTheory.Mum.PolTens GlobalTheory.TensBal in

theorem GlobalTheory.Mum.PolTens.tauBal_polTens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w hpr hc hw hpsi
  letI := PowLim.mod xe (symUnitOf W h)
  intro a
  have hA := transpose_mul_eq W h a
  intro u' hu' hn' y y'
  have htr := triv_span xe hpr hc (span_sigP W _ _ hA)
  rw [flat_sigP] at htr
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := htr
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at Q.M.isLB z
  have key := ros_sig hl hpr w hw _ _ u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', tv_sigP Q xe W _ _ (fun y => a • y) (fun y => star a • y) (PowLim.xe_smul xe _ a)
    (PowLim.xe_smul xe _ (star a)) z J y y'] at key
  have prr := prod_ros (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
    (DVR.cP D'.toPre (TK R) y) (DVR.cP D'.toPre (TK R) y') (isoV w z J J')
  have l₁ : DVR.cP D'.toPre (TK R) y ≫ PowLim.act pr hl (TensO.mat _ a) = DVR.cP D'.toPre (TK R) (a • y) := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  have l₂ : DVR.cP D'.toPre (TK R) y' ≫ PowLim.act pr hl (TensO.mat _ (star a)) =
      DVR.cP D'.toPre (TK R) (star a • y') := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  rw [l₁, l₂, ← DVR.cPoint_add, ← DVR.cPoint_add] at prr
  change ∏ k, isoV w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (PowLim.act pr hl (TensO.mat _ a))
    (PowLim.act pr hl (TensO.mat _ (star a))) k) ^ rosatiε k = _ at prr
  rw [prr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_pol xe w hpsi hJ hJ', tau_pol xe w hpsi hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have v0 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 0 = a • y + y' := rfl
  have v1 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 1 = a • y := rfl
  have v2 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 2 = y' := rfl
  have v3 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 3 = y + star a • y' := rfl
  have v4 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 4 = y := rfl
  have v5 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 5 = star a • y' := rfl
  rw [Fin.prod_univ_six] at key
  erw [v0, v1, v2, v3, v4, v5] at key
  simp only [e0, e1, e2, e3, e4, e5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem scalar_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  intro R _ _ _ Q D' r W pr xe w hpsi k hk ga' a' h' y
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  obtain ⟨J', hJ', iJ'⟩ := GlobalTheory.Mum.TensPos.exists_int D'.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hψ' : val (D'.psi y) (𝟙 _) z J' = E (a' y) * val (ga' y) (toUnit (TK R)).left z J' :=
    Units.ext (((h' y).2 (TK R) (𝟙 _) z J' hJ').trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have mg' : val (ga' y) (toUnit (TK R)).left z J' ∈ unitsS z := GlobalTheory.Mum.TensPos.val_mem D'.P z iJ' _ _ _
  have mτ : ∀ b c : Q.X, ∃ u ∈ unitsS z, val (Q.tau b c) (𝟙 _) z J = u * E (k b c) := fun b c => by
    obtain ⟨u, -, hu⟩ := hk b c
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ (lamPts (Q.c b) (Q.c c)) (fun i => ?_) negε u, ?_⟩
    · fin_cases i <;> exact Over.w _
    · rw [hu z J hJ, gm_unitOn, _root_.mul_comm]
  choose u hu eu using mτ
  have e := hpsi y z J J' hJ hJ'
  have hφ : ∀ k, tensφ pr k ≫ Q.B.hom = D'.P.A.hom := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases k <;> exact Over.w _
  have mw : gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) ∈ unitsS z := by
    refine gm_mem z (D'.c y).left
      (LB.wchart Q.M.L (tensφ pr) (fun k => J (D'.xK y ≫ tensφ pr k)) ⊓ D'.P.L.U (J' (D'.xK y)))
      ⟨Set.mem_iInter.2 fun k => ?_, iJ' _ (Over.w _)⟩ _
    have := iJ ((D'.c y).left ≫ tensφ pr k) (by rw [Category.assoc, hφ]; exact Over.w _)
    rw [← Category.assoc] at this
    exact this
  rw [hψ'] at e
  simp only [eu, mul_zpow, Finset.prod_mul_distrib] at e
  obtain ⟨v, hv, ev'⟩ := mul_mem (mul_mem (inv_mem mg') mw)
    (prod_mem fun i (_ : i ∈ Finset.univ) => prod_mem fun j (_ : j ∈ Finset.univ) => zpow_mem (hu (xe y i) (xe y j)) (W i j))
  refine ⟨v, hv, hE ?_⟩
  rw [map_mul, map_prod]
  simp only [map_prod, map_zpow]
  rw [show E v = _ from ev', eq_mul_inv_of_mul_eq e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.TensPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolScal

theorem exists_bilin (R : Type) [CommRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    (k : X → X → (FractionRing R)ˣ) (hs : ∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b)
    (ha : ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ, ∀ a b, ∃ u ∈ unitsK R, k a b = u * (B a b).toMul := by
  set H := unitsK R
  have h1 : ∀ u ∈ H, (QuotientGroup.mk' H) u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu
  let g : X → X → Additive ((FractionRing R)ˣ ⧸ H) := fun a b => Additive.ofMul (QuotientGroup.mk' H (k a b))
  have gs : ∀ a b, g b a = g a b := fun a b => by
    obtain ⟨u, hu, e⟩ := hs a b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul]
  have ga : ∀ a a' b, g (a + a') b = g a b + g a' b := fun a a' b => by
    obtain ⟨u, hu, e⟩ := ha a a' b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul, ofMul_mul]
  have gb : ∀ a b b', g a (b + b') = g a b + g a b' := fun a b b' => by
    rw [gs, ga, gs b, gs b']
  have gsa : ∀ (c : ℤ) a b, g (c • a) b = c • g a b := fun c a b =>
    map_zsmul (AddMonoidHom.mk' (fun a => g a b) (fun a a' => ga a a' b)) c a
  have gsb : ∀ (c : ℤ) a b, g a (c • b) = c • g a b := fun c a b => by
    rw [gs, gsa, gs]
  let F : X →ₗ[ℤ] X →ₗ[ℤ] Additive ((FractionRing R)ˣ ⧸ H) := LinearMap.mk₂ ℤ g ga gsa gb gsb
  let π : Additive (FractionRing R)ˣ →+ Additive ((FractionRing R)ˣ ⧸ H) := MonoidHom.toAdditive (QuotientGroup.mk' H)
  let bs := Module.Free.chooseBasis ℤ X
  let B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ :=
    bs.constr ℤ fun i => bs.constr ℤ fun j => Additive.ofMul (k (bs i) (bs j))
  have e : B.compr₂ π.toIntLinearMap = F := LinearMap.ext_basis bs bs fun i j => by
    simp [B, F, g, π]
  refine ⟨B, fun a b => ⟨k a b * ((B a b).toMul)⁻¹, ?_, by rw [inv_mul_cancel_right]⟩⟩
  have e1 : QuotientGroup.mk' H (B a b).toMul = QuotientGroup.mk' H (k a b) :=
    congrArg Additive.toMul (congrArg (fun C => C a b) e)
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' H _ = 1
  rw [map_mul, map_inv, ← e1, mul_inv_cancel]

end GlobalTheory.Mum.TensPolScal

namespace GlobalTheory.Mum.TensPolScal

theorem scalars_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ _ k hs ha hp r W hW a' h'
  obtain ⟨B, hB⟩ := exists_bilin R X k hs ha
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  let κ' : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j
  let P : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z i) (z j)).toMul ^ W i j
  let Q : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z j) (z i)).toMul ^ W i j
  have eP : ∀ z, Additive.ofMul (P z) = ∑ i, ∑ j, W i j • B (z i) (z j) := fun z => by
    simp only [P, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eQ : ∀ z, Additive.ofMul (Q z) = ∑ i, ∑ j, W i j • B (z j) (z i) := fun z => by
    simp only [Q, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eκ' : ∀ z, κ' z = P z * Q z := by
    intro z
    apply Additive.ofMul.injective
    rw [ofMul_mul, eP, eQ, ← Finset.sum_add_distrib]
    simp only [κ', κ, ofMul_prod, ofMul_zpow, ofMul_mul, ofMul_inv, ofMul_toMul, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    congr 1
    abel

  have hBs : ∀ a b, ∃ v ∈ unitsK R, (B b a).toMul = v * (B a b).toMul := by
    intro a b
    obtain ⟨w, hw, e⟩ := hs a b
    refine ⟨(u b a)⁻¹ * w * u a b, mul_mem (mul_mem (inv_mem (hu b a)) hw) (hu a b), ?_⟩
    rw [show (B b a).toMul = (u b a)⁻¹ * k b a by rw [eu b a, inv_mul_cancel_left], e, eu a b]
    group
  choose v hv ev using hBs
  have eQP : ∀ z, Q z = (∏ i, ∏ j, v (z i) (z j) ^ W i j) * P z := by
    intro z
    simp only [Q, P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [ev (z i) (z j), mul_zpow]
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add, LinearMap.add_apply]
    abel
  have κp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (κ x : FractionRing R) = algebraMap R _ s := fun x hx => by
    have := mem_of_unit _ ((unitsK R).inv_mem (hu x x)) (hp x hx)
    rwa [eu x x, inv_mul_cancel_left] at this
  have κ'p := GlobalTheory.Mum.TPos.tensor_pos R X κ κn κc κp W hW

  have Pp : ∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (P z : FractionRing R) = algebraMap R _ s := by
    intro z hz
    have hd : (∏ i, ∏ j, v (z i) (z j) ^ W i j) ∈ unitsK R :=
      prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hv _ _) _
    have e2 : P z ^ 2 = (∏ i, ∏ j, v (z i) (z j) ^ W i j)⁻¹ * κ' z := by
      rw [eκ', eQP, mul_left_comm, inv_mul_cancel_left, pow_two]
    obtain ⟨s, hsm, es⟩ := mem_of_unit _ ((unitsK R).inv_mem hd) (κ'p z hz)
    rw [← e2, Units.val_pow_eq_pow_val] at es
    have hint : IsIntegral R ((P z : (FractionRing R)ˣ) : FractionRing R) :=
      IsIntegral.of_pow (by norm_num : 0 < 2) (es ▸ isIntegral_algebraMap)
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have ht2 : t ^ 2 = s := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [map_pow, ht, es]
    exact ⟨t, (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 (ht2 ▸ hsm), ht.symm⟩
  have Pn : ∀ z, P (-z) = P z := fun z => by
    apply Additive.ofMul.injective
    simp [eP]
  have Pc : ∀ x y w, P (x + y + w) * P x * P y * P w = P (x + y) * P (x + w) * P (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, eP, ← Finset.sum_add_distrib, ← smul_add, Pi.add_apply, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have Pt := GlobalTheory.QuadTend.finite_not_mem_pow R (Fin r → X) P Pn Pc Pp
  have ea : ∀ z, ∃ v ∈ unitsK R, a' z = v * P z := fun z => by
    obtain ⟨w, hw, e⟩ := h' z
    refine ⟨w * ∏ i, ∏ j, u (z i) (z j) ^ W i j,
      mul_mem hw (prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hu _ _) _), ?_⟩
    rw [e, _root_.mul_assoc]
    congr 1
    simp only [P, eu, mul_zpow, Finset.prod_mul_distrib]
  refine ⟨fun z hz => ?_, fun n => (Pt n).subset fun z hz hm => hz ?_⟩
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw (Pp z hz)
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw hm

end GlobalTheory.Mum.TensPolScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_values_facts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), TensFacts W (cmp T ν ν') (chi T ν ν') (wv T ν ν') := by
  first | exact @GlobalTheory.Mum.TensTor.tensFacts_holds | exact GlobalTheory.Mum.TensTor.tensFacts_holds | (intros; apply GlobalTheory.Mum.TensTor.tensFacts_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilySectionEquivarianceSmulOfNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.ScaleEqv.eqv_scale | exact GlobalTheory.Mum.ScaleEqv.eqv_scale | (intros; apply GlobalTheory.Mum.ScaleEqv.eqv_scale <;> assumption)
end

