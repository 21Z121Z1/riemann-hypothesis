import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0584
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0577
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0571
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0090
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0107
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AutomorphicArithmetic.ResidueCharacters.StarS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0113
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FnAlgClosedCore
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem fnAlgClosed_core_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hR : _root_.GlobalTheory.CovTop.RowsTAlt p) (j : ℕ) (hj : InR D j) : FnAlgClosed (p.T.Q.Xo j) p.T.Q.c := by
  have hc := hR.1.ties.core
  have hpin : p.T.Q.Pins := hc.laws.pins
  have hpos : 0 < D.host.g 0 * D.host.g 1 * D.host.pde :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) D.host.pde_prime.pos
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D p.T.Q hpin hc.canon _ hpos hc.field₁.curve j hj p.T.Q.l
    (p.T.Q.Xo j) p.T.Q.c hpin.2.1.2 ?_ rfl
  rw [hpin.2.1.1]
  exact Dvd.intro _ rfl
end GlobalTheory.CoreDesc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
namespace GlobalTheory.CovTop.Sizes
theorem hostN_alt : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  intro M
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := eventually_scale he (22 + |Fm.Ct|) M
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)
  refine ⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := hx0 x ((le_max_left _ _).trans hle)
  have a5 : 5 ≤ x ^ (Fm.ez / 5) := hx2 x ((le_max_right _ _).trans hle)
  have hsz : (Fm.L x ι).sc.ez = Fm.ez := Fm.toFamCore.L_ez x ι
  have hsx : (Fm.L x ι).sc.x = x := Fm.L_x x ι hx
  have hse : (Fm.L x ι).sc.eps = eps := Fm.L_eps x ι
  have hsL : (Fm.L x ι).sc.L = x ^ eps := by unfold Scale.L; rw [hsx, hse]
  have hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1 := fun k => by
    have hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ) := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    have := (Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)
    linarith
  refine hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fm.Ct_eq]; linarith [le_abs_self Fm.Ct]
  · rwa [hsL]
  · rwa [hsL]
  · rwa [hsx]
  · unfold Scale.b; rwa [hsL, hsx]
  · rwa [hsx, hsz]
  · rwa [hsx]
end GlobalTheory.CovTop.Sizes
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerOfAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
theorem kerOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p hR hM w hw j => ?_⟩⟩⟩
  intro ρ hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hpl := placesAt (j := j) hw hρ hpin
  have hl : (Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w) = Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w) := by
    rw [(Fm.ex x hx i).nch.twI_l, Formalism.L2.G.ServJoint.plc_plEq]
  have hpD : ∀ P, P ∈ (Fm.D x i).ntw.pD ((Fm.ex x hx i).nch.twI w) ↔
      ((ownAt (Fm.D x i) ((Fm.D x i).plEq w) : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, (Fm.D x i).ntw.pD_eq, ownAt, ← hl]
    rfl
  have hQ : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.Q = plW p w := by
    ext P
    rw [hpl.1 P, hpD P]
    unfold plW GlobalTheory.OnTies.placesOver
    classical
    rw [Finset.mem_filter]
    rfl
  have hwt : (Fm.D x i).plEq w ∈ (R2 p).twPl := hw
  obtain ⟨ω, φ, hK⟩ := GlobalTheory.OnCmp.exists_baseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on
  obtain ⟨χ, ξR, hD⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on ω φ hK
  have hχ : χ = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi :=
    GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ hD.chr (hl ▸ hpin.delta _ j _)
  subst hχ
  have hω := hρ.weil_base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at hω
  refine ⟨hBo, hQ, ξR, φ, { hD with weil := hω }⟩
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latSmallGen' : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.latSmallGen_alt | exact _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatZeroLine
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos
namespace GlobalTheory.LineOffT
variable {D : D7}
theorem lat_zero_line_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v' : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v') (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), f.c.Is → v'.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v' → ShapeOff v' o → GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v' o G → GlobalTheory.MiTop.PrimTop (c := f.c) v'.tP o.ζ₀ → ∀ x : GlobalTheory.FinPl.Pl D, x ∉ v'.gP → x ∉ v'.tP → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ x.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = x), ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) (v'.N 0) (· = x) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = x)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B k _ _ _ _ ι v o n G pl hc _ _ sh _ _ hb hp x _ hx u'' hu'' a ha
  have hTp : (D.mem u'').A.T.Prime := (D.mem u'').A.T_prime
  have hcop : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.mem u'').A.T := by
    obtain ⟨P, hP⟩ := exists_place D.host.E hTp
    refine ((Nat.Prime.coprime_iff_not_dvd hTp).2 fun ⟨t, ht⟩ => hW.aa P (Or.inr (Or.inr ⟨u'', hP⟩)) ?_).symm
    rw [ht, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hP
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hc.std
  have hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE f.c.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x) := fun s hs => by
    rw [(hα x).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have uξ := isU_xi_of_prime hTp hu'' (D.T_ne_d u'') hcop
  have uα := isU_alpha_of_prime hTp hu'' (UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u'')) (D.T_ne_q u'') (D.T_ne_d u'') hcop sh.pre.line (hα x).1
  have ug : IsU x (incA D (W.S.X.B.g : D.host.E)) := by
    refine isU_nat (UnitAt.notMem_of_coprime hu'' ?_)
    rw [W.S.X.g_eq]
    exact Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hTp).2 (D.T_ne_g u'' 0).symm)
      ((Nat.coprime_primes (D.host.g_prime 1) hTp).2 (D.T_ne_g u'' 1).symm)
  have uc : IsU x (cU α : AE D) := uα.conj
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 ⟨0, hr⟩ rfl
  have hI := GlobalTheory.LineIdeal.all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 hx (hα x).1 hψ 0 D.R.rS h₀ (D.R.rS - 1) ⟨0, hr⟩ (by simp only; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  rw [← mul_assoc (α * α), ← mul_assoc ((xiU D * α * cU α) ^ _)] at hI
  have uK : IsU x (((xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) := by
    have h1 : IsU x (((xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := (uξ.mul uc).inv (xiU D * cU α).mul_inv
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact (((uξ.mul uα).mul uc).pow _).mul ((uα.mul uα).mul ((uα.mul h1).pow _))
  generalize (xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI uK
  have uS : IsU x (incA D (-s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS))) := by
    have h1 : IsU x (incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) := by
      rw [map_mul, map_pow, map_pow]
      exact (IsU.pow (u := incA D D.host.xi0) uξ _).mul (ug.pow _)
    rcases hs with rfl | rfl
    · rw [neg_one_mul, map_neg]; exact h1.neg
    · rwa [neg_neg, one_mul]
  have hg0 : (W.S.X.B.g : D.host.E) ≠ 0 := by
    rw [W.S.X.g_eq]
    exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  obtain ⟨w, hw⟩ : ∃ w, w = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := hw ▸ mul_ne_zero hs0 (mul_ne_zero hμ (pow_ne_zero _ hg0))
  have hlw : -s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS) = lam * w := by
    rw [hw]
    linear_combination (-s * (W.S.X.B.g : D.host.E) ^ D.R.rS) * n1
  rw [← hw] at he
  rw [hlw, map_mul] at uS
  have e1 : incA D w * incA D w⁻¹ = 1 := (inU w hw0).mul_inv
  have hy : (fun i => a * incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      colMul B.d.jX ⟨0, hr⟩ (incA D w⁻¹ * a) := by
    funext i
    change _ = _ * incA D (B.d.e i ⟨0, hr⟩)
    rw [he, map_mul]
    generalize incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i))) = t
    linear_combination (-a * t) * e1
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI (incA D w⁻¹ * a) (Ideal.mul_mem_left _ _ ha)
  rw [← hj] at h1
  refine (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hy)).trans (h1.trans ?_)
  rw [(uK.mul uS) _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))]
  have e2 := (K * inU lam hlam).mul_inv
  rw [Units.val_mul, inU_val] at e2
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D w * incA D w⁻¹ * a) * e2 + a * e1
end GlobalTheory.LineOffT
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_local_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W) := by
  first | exact @_root_.GlobalTheory.FamTrace.levTrace_mem_alt | exact _root_.GlobalTheory.FamTrace.levTrace_mem_alt | (intros; apply _root_.GlobalTheory.FamTrace.levTrace_mem_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelProd
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
theorem GlobalTheory.LevProd.level_prod_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ Up : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), Up ≤ GfC _ ∧ IsCompact (Up : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ (H : ∀ i, Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) (φ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)), (∀ i, H i ≤ KO (J.G i).k _ ∧ MeasurableSet (H i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (H i).relIndex (KO (J.G i).k _) ≠ 0 ∧ (J.E i).wt j (α i) = ((((J.E i).m j (H i)).toReal⁻¹ : ℝ) : ℂ)) ∧ (∀ g ∈ Up, ∀ i, φ g i ∈ KO (J.G i).k _) ∧ (∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ Up, φ g = x) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hA j hj
  refine ⟨_root_.GlobalTheory.LevProd.upperLevelSubgroup a (j := j) (by omega), _root_.GlobalTheory.LevProd.upperLevelSubgroup_le_GfC a j (by omega), _root_.GlobalTheory.T.is_compact_upper_level_subgroup W hW u a ha hA j (by omega), fun t J hJ α => ?_⟩
  refine ⟨_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j (by omega) α, _root_.GlobalTheory.LevProd.localHomProduct J j (by omega), fun i => ⟨?_, ?_, ?_, _root_.GlobalTheory.LevProd.wt_eq_inv_measure_levelSubgroupAtPlace J j (by omega) α i⟩,
    _root_.GlobalTheory.T.true_geometry_lattice_step_value_alt W hW u a ha hA j (by omega) t J hJ, _root_.GlobalTheory.T.true_geometry_lattice_level_alt W hW u a ha hA j (by omega) t J hJ α,
    _root_.GlobalTheory.T.true_geometry_lattice_twist_alt W hW u a ha hA j (by omega) t J hJ α⟩
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).1
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).2.1
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).2.2
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogSumBadPrimesLe
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.BadLog
variable {D : D7} {L : SizeData₂ D}
theorem logSum_badPrimes_le_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p _ Y _ C => logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ C * zBase (Fm.L x ι) :=
  fun h => Closed.imp h fun Fm _ _ _ => ⟨2 * |Fm.CYL| + 17, by positivity, 0, fun x hx _ ι p _ i _ Y hY => by
    obtain ⟨a, b⟩ := log_level_le (Fm.params x hx ι)
    rw [Fm.params_CYL] at b
    exact (logSum_le_log a fun q hq => dvd_of_mem_badPrimes p.fw.laws.pins hY.1 hq).trans b⟩
end GlobalTheory.BadLog
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowOfCoverHypotheses
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.LowCover
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem low_of_cover_hypotheses : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LowDefectCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition → _root_.GlobalTheory.CovTop.MapsCondition → _root_.GlobalTheory.CovTop.CoverRank → _root_.GlobalTheory.CovTop.MinimalGenerator → _root_.GlobalTheory.CovTop.FlatnessCondition → _root_.GlobalTheory.CovTop.UniformLowerBound → _root_.GlobalTheory.CovTop.LiftLowBound := by
  intro hS hD hE hG hR hM hK hGm hF hU
  refine Closed.imp (((((((((hS.and hD).and hE).and hG).and hR).and hM).and hK).and hGm).and hF).and hU) ?_
  intro eps Fm CH _ hh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨CS, -, aS⟩, CD, -, aD⟩, _, -, aE⟩, _, -, aG⟩, _, -, aR⟩, _, -, aM⟩, _, -, aK⟩, _, -, aGm⟩,
    CF, hCF, aF⟩, CU, hCU, aU⟩ := hh
  refine ⟨max CD (2 * (CF + CU) + 9), le_max_of_le_right (by linarith), ?_⟩
  obtain ⟨x0, h⟩ := ((((((((aS.and aD).and aE).and aG).and aR).and aM).and aK).and aGm).and aF).and aU
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨bS, bD⟩, bE⟩, bG⟩, bR⟩, bM⟩, bK⟩, bGm⟩, bF⟩, bU⟩ := h x hx hle ι p hp
  have hS' := bS i
  have hE0 : 0 ≤ unitE p := by obtain ⟨a, b, -⟩ := hS'; linarith
  rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with heq | hlt
  · exact lowAt_mono (bD i heq) (le_max_left _ _) hE0
  · obtain ⟨Y, hY⟩ := bE i hlt
    exact lowAt_mono (lowAt_of_cover p i _ CS CF CU hCF hCU hS' Y (bG i hlt Y hY) (bR i hlt Y hY) (bM i hlt Y hY)
      (bK i hlt Y hY) (bGm i hlt Y hY) (bF i hlt Y hY) (bU i hlt Y hY)) (le_max_right _ _) hE0
end GlobalTheory.CovTop.LowCover
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NStarS
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.starSF_of_prints (hP : Hypotheses₂) : _root_.UpperTheory.N.StarSelfDualCondition := by
  obtain ⟨A, B, hA, hB, h⟩ := _root_.UpperTheory.N.exists_nonneg_c_constants_of_prints hP
  exact _root_.UpperTheory.N.starSF_of_rowC_alt A B hA hB h
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPathStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onto_x_of_all_estimates : _root_.GlobalTheory.BigOn.TwoRunsStatement → _root_.GlobalTheory.BigOn.RationalityStatement' → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → _root_.GlobalTheory.BigOn.TwistStatement' → _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  first | exact @_root_.GlobalTheory.BigOn.OntoPath.onto_path_alt | exact _root_.GlobalTheory.BigOn.OntoPath.onto_path_alt | (intros; apply _root_.GlobalTheory.BigOn.OntoPath.onto_path_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRecStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_at_twisted_places_of_max_geo : _root_.GlobalTheory.BigOn.MaximalityStatement → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) := by
  first | exact @_root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs | exact _root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs | (intros; apply _root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs <;> assumption)
end
end

