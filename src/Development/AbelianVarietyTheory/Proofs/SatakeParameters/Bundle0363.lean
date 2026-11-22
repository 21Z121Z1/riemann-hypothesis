import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0354
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0357
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CongSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def zchar {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) : Multiplicative (ZMod N) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]

theorem zchar_apply {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) (x : Multiplicative (ZMod N)) :
    zchar ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem sum_roots {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hk : k < N) :
    ∑ i : Fin N, (ζ ^ (i : ℕ)) ^ k = if k = 0 then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ i) ^ k)]
  simp_rw [← pow_mul, mul_comm _ k, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ζ ^ k ≠ 1 := fun e => h (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd k).1 e) hk)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

def stab (W : Wt E n) (f : algForms W) : Subgroup (UA E n) where
  carrier := {x | ∀ v g, f.1 v (g * x) = f.1 v g}
  mul_mem' {x y} hx hy v g := by rw [← mul_assoc, hy, hx]
  one_mem' v g := by rw [mul_one]
  inv_mem' {x} hx v g := by
    have := hx v (g * x⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem stab_level (W : Wt E n) (f : algForms W) (C : Subgroup (UA E n)) (hC : C ≤ finU E n)
    (hc : IsCompact (C : Set (UA E n))) (ho : ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E n ⊆ C) :
    IsCompact ((C ⊓ stab W f : Subgroup (UA E n)) : Set (UA E n)) ∧
      ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E n ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := by
  obtain ⟨N₁, hN₁, h1, hN₁C⟩ := ho
  have hsm := isSmooth_algRep W f
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hsm
  have hfix : ∀ x (hx : x ∈ finU E n), x ∈ t → x ∈ stab W f := by
    intro x hx hxt v g
    have : (⟨x, hx⟩ : finU E n) ∈ {k : finU E n | algRep W k f = f} := by rw [← hte]; exact hxt
    exact congrArg (fun F : algForms W => F.1 v g) this
  have h1t : (1 : UA E n) ∈ t := by
    have : (1 : finU E n) ∈ {k : finU E n | algRep W k f = f} := by simp
    rw [← hte] at this; exact this
  have hN : N₁ ∩ t ∩ finU E n ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := fun x ⟨⟨hx1, hxt⟩, hxf⟩ =>
    ⟨hN₁C ⟨hx1, hxf⟩, hfix x hxf hxt⟩
  refine ⟨?_, N₁ ∩ t, hN₁.inter ht, ⟨h1, h1t⟩, hN⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (((C ⊓ stab W f).subgroupOf C : Subgroup C) : Set C) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (((hN₁.inter ht).preimage continuous_subtype_val).mem_nhds ⟨h1, h1t⟩) ?_)
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hN ⟨hx, hC x.2⟩)
  have hHc := Subtype.isCompact_iff.1 (Subgroup.isClosed_of_isOpen _ hHo).isCompact
  convert hHc using 1
  ext x; constructor
  · intro hx; exact ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact Subgroup.mem_subgroupOf.1 hy

def opL (s : UA E n →₀ ℂ) : Module.End ℂ (UA E n → ℂ) where
  toFun := opOf (RU E n) s
  map_add' φ ψ := by simp [opOf, Finsupp.sum, Finset.sum_add_distrib, smul_add]
  map_smul' c φ := by simp [opOf, Finsupp.sum, Finset.smul_sum, smul_comm c]

end GlobalTheory.CongSc

namespace GlobalTheory.CongSc

end GlobalTheory.CongSc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentityStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_contraction_scalars_identity : ∀ (m m' g g' k k' x x' A A' Δ Δ' : ℂ) (n n' c c' : ℤ), m ≠ 0 → m' ≠ 0 → g ≠ 0 → g' ≠ 0 → k ≠ 0 → k' ≠ 0 → x ≠ 0 → x' ≠ 0 → A ≠ 0 → A' ≠ 0 → Δ ≠ 0 → Δ' ≠ 0 → (g' * m' * k') * (g * m * k)⁻¹ * (Δ⁻¹ * A) ^ (-c) * (Δ'⁻¹ * A') ^ c' * ((Δ⁻¹ * A) ^ n' * (Δ'⁻¹ * A') ^ (-n))⁻¹ * (k * x' / (k' * x)) = (m⁻¹ * A ^ (-n')) * (m' * A' ^ n) * (x⁻¹ * g⁻¹ * Δ ^ (n' + c) * A ^ (-c)) * (x' * g' * Δ' ^ (-(n + c')) * A' ^ c') := by
  first | exact @GlobalTheory.TwV.DelB.pullback_contraction_scalars | exact GlobalTheory.TwV.DelB.pullback_contraction_scalars | (intros; apply GlobalTheory.TwV.DelB.pullback_contraction_scalars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePairStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  first | exact @GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | exact GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | (intros; apply GlobalTheory.TwV.DelB.pullbackScalar_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFramesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_then_frame_substitution_eq_changed_frames : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  first | exact @GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe | exact GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe | (intros; apply GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_badPrimes_coprime_residueChar : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  first | exact @GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | exact GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | (intros; apply GlobalTheory.TwV.Xc.SBad.bad_prime_to_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realising_polynomial_blockwise_homogeneous : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  first | exact @GlobalTheory.TwV.DelA.BlockHom.realises_blockHom | exact GlobalTheory.TwV.DelA.BlockHom.realises_blockHom | (intros; apply GlobalTheory.TwV.DelA.BlockHom.realises_blockHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  first | exact @GlobalTheory.Port.site_labels_with_stepZero_classMap | exact GlobalTheory.Port.site_labels_with_stepZero_classMap | (intros; apply GlobalTheory.Port.site_labels_with_stepZero_classMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZeroStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_localIdentifications_eq_stepZero : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  first | exact @GlobalTheory.Proof.LocOfSite.loc_eq_step0 | exact GlobalTheory.Proof.LocOfSite.loc_eq_step0 | (intros; apply GlobalTheory.Proof.LocOfSite.loc_eq_step0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siteSystem_ranks_eq_datum_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  first | exact @GlobalTheory.TwV.DelB.sysS_ranks | exact GlobalTheory.TwV.DelB.sysS_ranks | (intros; apply GlobalTheory.TwV.DelB.sysS_ranks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtPStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  first | exact @GlobalTheory.TwV.LbB.lbAtB_inTw | exact GlobalTheory.TwV.LbB.lbAtB_inTw | (intros; apply GlobalTheory.TwV.LbB.lbAtB_inTw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetCoupledEqProdLocalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacter_det_coupled_eq_prod_local : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU → ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ'.1) =
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'' P).1 : t.X.Eˣ) : t.X.E))) := by
  first | exact @GlobalTheory.CplMuDet.muOf_det_cpl | exact GlobalTheory.CplMuDet.muOf_det_cpl | (intros; apply GlobalTheory.CplMuDet.muOf_det_cpl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepChartsPlacesFirstFactorEqStepZeroStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharts_places_firstFactor_eq_stepZero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧ ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  first | exact @GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero | exact GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero | (intros; apply GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero <;> assumption)
end

