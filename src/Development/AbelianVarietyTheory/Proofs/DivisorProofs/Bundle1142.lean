import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.CechPic

theorem exists_generating_secs_of_cls_eq : ∀ (X : Scheme.{0}) (L A : LB X) (hL : L.IsLB) (hA : A.IsLB), cls L hL = cls A hA → ∀ (ι : Type) (u : ι → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ v : ι → A.Sec, ⨆ i, nonzeroLocus (v i) = ⊤ := by
  intro X L A hL hA h ι u hu
  have hiso : LBIso A L := (cls_eq_iff hA hL).1 h.symm
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hA hL hiso (u i)
  refine ⟨v, ?_⟩
  simp only [hv]
  exact hu

end GlobalTheory.CechPic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ v ∈ (principalLevelFrame.FinTyp.conjT π).S, v ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v := by
  first | exact @GlobalTheory.OccRowVec.exists_vec_of_occRows | exact GlobalTheory.OccRowVec.exists_vec_of_occRows | (intros; apply GlobalTheory.OccRowVec.exists_vec_of_occRows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.IrrInfChar

theorem cap_commute_act' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ) (u : ℂ)
    (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

theorem exists_scalar {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {V : Submodule ℂ (Sm E a)}
    (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_hasInfCharGL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) : ∃ μ, HasInfCharGL V τ μ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (fun o => cap_commute_act' τ u o)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (τ : E →+* ℂ), (∀ x : CuspSub E N, ∃ μ, x.HasInfChar τ μ) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ μ, HasInfCharGL V τ μ := by
  intro E _ _ _ N τ
  refine ⟨fun x => ⟨(CG.mk x).infChar τ, ?_⟩, fun V hV => exists_hasInfCharGL hV τ⟩
  exact hasInfChar_infChar_of_commute E N (fun τ u o => cap_commute_act' τ u o) (CG.mk x) τ

end GlobalTheory.ResW.IrrInfChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem dchi_absC_one_finrank (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (s : ℂ) :
    dchi (GlobalTheory.CuspRep.Model.absC E s) 1 = s * (Module.finrank ℚ E : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ :=
    s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (GlobalTheory.CuspRep.Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [GlobalTheory.CuspRep.Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  have h2 : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  rw [h, h2]
  simp [A, mul_comm]

theorem exists_abs_cpow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  intro E _ _ _ z
  refine ⟨GlobalTheory.CuspRep.Model.absC E z, fun a φ => ?_, fun v => ⟨fun x hx => Units.ext ?_, ?_⟩, fun x => ?_, fun hz => ?_⟩
  · unfold zc
    rw [lie_mulChi]
    have e : (Matrix.of (fun i j : Fin a => if i = j then (1 : Cinf E) else 0)).trace = (a : ℝ) • (1 : Cinf E) := by
      simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
    rw [e, map_smul, dchi_absC_one_finrank]
    congr 3
    simp only [Complex.real_smul, Complex.ofReal_natCast]; ring
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v x)) = 1
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change ‖Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖ =
      ‖Complex.exp ((z.re : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖
    rw [Complex.norm_exp, Complex.norm_exp]; simp
  · have e : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
    conv_lhs => rw [e]
    rfl

end GlobalTheory.ResW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.HeckeExtend

theorem exists_int_of_mem_intF : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  intro F _ _ y m hm hy
  obtain ⟨c, hc, e⟩ := hy
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y / m) ≤ 1 := by
    intro v
    have h1 : (y : v.adicCompletion F) = ((m : F) : v.adicCompletion F) * c v := by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) e
      simp only [nsmul_eq_mul] at this
      have hL : (algebraMap F (AF F) y).2 v = (y : v.adicCompletion F) := rfl
      have hm' : ((m : FiniteAdeleRing (𝓞 F) F)) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) :=
        (map_natCast _ m).symm
      have hR : ((m : FiniteAdeleRing (𝓞 F) F) * c) v = ((m : F) : v.adicCompletion F) * c v := by
        rw [hm']; rfl
      rw [← hL, ← hR]
      exact this
    have h2 : v.valuation F y = v.valuation F (m : F) * Valued.v (c v) := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h1, map_mul,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hv0 : v.valuation F (m : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hmF
    rw [map_div₀, h2, mul_div_cancel_left₀ _ hv0]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hc v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y / (m : F)) key
  refine ⟨r, ?_⟩
  have : ((r : 𝓞 F) : F) = y / m := hr
  rw [this, mul_div_cancel₀ _ hmF]

end GlobalTheory.HeckeExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntersectionFormPicardDoubleSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_interForm_dbl : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∃ T : MultilinearMap ℤ (fun _ : Fin (Y.dim + 1) => Pic W.Z) ℤ, (∀ (σ : Equiv.Perm (Fin (Y.dim + 1))) (y : Fin (Y.dim + 1) → Pic W.Z), T (y ∘ σ) = T y) ∧ ∀ y : Fin (Y.dim + 1) → CartierDiv W.Z, T (fun i => toPic (y i)) = W.num y := by
  intro F _ Y W hW
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hv : DiffVanish (Y.dim + 1 + 1) (chiPic F (structureModule W.Z)) :=
    diffVanish_chiPic_of_isProjOver (algebraΓOfHom_algebraMap (W.p₁ ≫ Y.str)) (structureModule W.Z) W.proj
      (by rw [GlobalTheory.QCoh.suppDim_structureModule]; exact hW)
  refine ⟨hv.form, fun σ y => hv.form_comp_perm y σ, fun y => ?_⟩
  rw [hv.form_apply _ 0]
  show _ = interNum F (structureModule W.Z) fun i => toLB (y i)
  rw [interNum_eq_multiDiff F _ fun i => isLB_toLB (y i)]
  rfl

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLattiStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  first | exact @GlobalTheory.TraceCorrection.exists_pair | exact GlobalTheory.TraceCorrection.exists_pair | (intros; apply GlobalTheory.TraceCorrection.exists_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCm
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkew

theorem exists_re_pos_of_congr_diagonal {n : ℕ} (H Q : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hQ : Q.det ≠ 0) (hd : Qᵀ * H * Q.map star = Matrix.diagonal δ)
    (u : Fin n → ℂ) (hu : 0 < (u ⬝ᵥ H *ᵥ star u).re) : ∃ i, 0 < (δ i).re := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨v, rfl⟩ : ∃ v, Q *ᵥ v = u :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hQ)) u
  have hs : star (Q *ᵥ v) = Q.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : (Q *ᵥ v) ⬝ᵥ H *ᵥ star (Q *ᵥ v) = v ⬝ᵥ (Qᵀ * H * Q.map star) *ᵥ star v := by
    rw [hs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Qᵀ,
      Matrix.vecMul_transpose]
  rw [key, hd] at hu
  have h2 : v ⬝ᵥ Matrix.diagonal δ *ᵥ star v = ∑ i, δ i * (Complex.normSq (v i) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Pi.star_apply]
    ring
  rw [h2, Complex.re_sum] at hu
  refine hu.not_ge (Finset.sum_nonpos fun i _ => ?_)
  rw [Complex.re_mul_ofReal]
  exact mul_nonpos_of_nonpos_of_nonneg (hneg i) (Complex.normSq_nonneg _)

theorem exists_algebraMap_eq_of_fixed {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E) {ξ : E} (hξ0 : ξ ≠ 0) (hξ : σ ξ = -ξ) {e : E}
    (he : σ e = e) : ∃ a : F, algebraMap F E a = e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  set V : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id) with hV
  have mem : ∀ x, x ∈ V ↔ σ x = x := fun x => by
    simp [hV, sub_eq_zero]
  have hle : Submodule.span F {(1 : E)} ≤ V := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem, map_one]
  have hne : V ≠ ⊤ := by
    intro htop
    have : ξ ∈ V := htop ▸ Submodule.mem_top
    rw [mem, hξ] at this
    have h2' : (2 : E) * ξ = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h2' with h | h
    · exact two_ne_zero h
    · exact hξ0 h
  have hlt := Submodule.finrank_lt hne
  have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have : e ∈ Submodule.span F {(1 : E)} := heq ▸ (mem e).mpr he
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one, ha]⟩

theorem re_embedding_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (τ : E →+* ℂ) (a : F) :
    (τ (algebraMap F E a)).re =
      ((emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).1 (algebraMap F E a)).re := by
  have h1 := congrArg (fun f : F →+* ℂ => f a) (emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).2
  simp only [RingHom.comp_apply] at h1
  rw [h1]
  rcases InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h
  · rw [h, RingHom.comp_apply]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, Complex.conj_re]

theorem exists_isotropic_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r s : ℕ), (∀ i j, σ (J j i) = -J i j) →
    (∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) → 1 ≤ r → 1 ≤ s → 3 ≤ n →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  intro F E _ _ _ _ _ σ B hcm n J r s hJ hsig hr hs hn
  obtain ⟨hTR, hTC, h2, hconj⟩ := hcm
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ₀.injective (by rw [hconj, hconj, star_star])
  by_cases hd : J.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    refine ⟨fun i => σ (v i), fun h => hv0 (funext fun i => ?_), ?_⟩
    · have := congrArg σ (congrFun h i)
      simpa [hσσ] using this
    · have : (fun i => σ ((fun i => σ (v i)) i)) = v := funext fun i => hσσ _
      simp only [form]
      rw [this, hv, dotProduct_zero]
  haveI := hTR
  haveI := hTC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ a, σ a = IsCMField.complexConj E a := fun a =>
    τ₀.injective (by rw [hconj, IsCMField.complexEmbedding_complexConj]; rfl)
  obtain ⟨x₀, hx₀⟩ : ∃ x, σ x ≠ x := by
    by_contra hno
    push_neg at hno
    apply IsCMField.complexConj_ne_one E
    ext x
    rw [← hcc, hno]
    rfl
  set ξ := x₀ - σ x₀ with hξdef
  have hξ : σ ξ = -ξ := by rw [hξdef, map_sub, hσσ]; ring
  have hξ0 : ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx₀)
  set G : Matrix (Fin n) (Fin n) E := ξ • J with hG
  have hform : ∀ x, GlobalTheory.UTrans.hf (σ : E →+* E) G x x = ξ * form σ J x x := fun x => by
    simp only [GlobalTheory.UTrans.hf, form, dotProduct, Matrix.mulVec, hG, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [AlgHom.coe_toRingHom]
    ring
  have hherm : GlobalTheory.UTrans.IsHerm (σ : E →+* E) G :=
    { invol := hσσ
      ne_id := ⟨x₀, hx₀⟩
      herm := fun a b => by
        simp only [AlgHom.coe_toRingHom, hG, Matrix.smul_apply, smul_eq_mul, map_mul, hξ, hJ]
        ring
      det_ne := by
        rw [hG, Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ hξ0) hd }
  have hh : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hherm.herm a b]
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, AlgHom.coe_toRingHom, hcc]
  obtain ⟨P, d, hP, hPg, hdfix, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hh
  have hPg' : Pᵀ * G * P.map σ = Matrix.diagonal d := by
    rw [← hPg]; congr 2; ext a b; simp [ReciprocityTheory.ChartRestriction.G.FD.cc, hcc]
  have hdσ : ∀ i, σ (d i) = d i := fun i => by
    rw [hcc]; exact hdfix i
  have hdiag : ∀ i, GlobalTheory.UTrans.hf (σ : E →+* E) G (fun a => P a i) (fun a => P a i) = d i := fun i => by
    have := congrFun (congrFun hPg' i) i
    rw [Matrix.diagonal_apply_eq] at this
    rw [← this]
    simp only [GlobalTheory.UTrans.hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul, AlgHom.coe_toRingHom]
    exact Finset.sum_comm

  have hsignE : ∀ w : InfinitePlace F,
      (∃ i, 0 < ((B.emb w).1 (d i)).re) ∧ ∃ j, ((B.emb w).1 (d j)).re < 0 := by
    intro w
    set φ : E →+* ℂ := (B.emb w).1 with hφ
    obtain ⟨hrs, A, hA⟩ := hsig w
    have hφσ : ∀ x, φ (σ x) = star (φ x) := hconj φ
    have hQ : (P.map φ).det ≠ 0 := by
      have h := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero φ).mpr hP
    have hdQ : (P.map φ)ᵀ * G.map φ * (P.map φ).map star = Matrix.diagonal (fun i => φ (d i)) := by
      have e1 : (P.map φ).map star = (P.map σ).map φ := by
        ext a b
        simp [hφσ]
      rw [e1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPg',
        Matrix.diagonal_map (map_zero φ)]
    set c : ℂ := -Complex.I * φ ξ with hc
    have hGM : G.map φ = c • (Complex.I • J.map φ) := by
      ext a b
      simp only [hG, hc, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      linear_combination (φ ξ * φ (J a b)) * Complex.I_sq
    have hcol : ∀ k, (fun a => A a k) ⬝ᵥ G.map φ *ᵥ star (fun a => A a k) =
        c * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) k k := by
      intro k
      rw [← hA, hGM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
        Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hφξ : (φ ξ).re = 0 := by
      have h1 := congrArg Complex.re (hφσ ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.star_def, Complex.conj_re] at h1
      linarith
    have hφξ0 : (φ ξ).im ≠ 0 := by
      intro him
      apply hξ0
      apply φ.injective
      rw [map_zero]
      exact Complex.ext hφξ him
    have hcre : c.re = (φ ξ).im := by simp [hc, hφξ]
    have pos : ∀ u, 0 < (u ⬝ᵥ G.map φ *ᵥ star u).re → ∃ i, 0 < (φ (d i)).re :=
      fun u hu => exists_re_pos_of_congr_diagonal _ _ _ hQ hdQ u hu
    have neg : ∀ u, (u ⬝ᵥ G.map φ *ᵥ star u).re < 0 → ∃ i, (φ (d i)).re < 0 := fun u hu => by
      obtain ⟨i, hi⟩ := exists_re_pos_of_congr_diagonal (-(G.map φ)) _ (fun i => -φ (d i)) hQ
        (by rw [Matrix.mul_neg, Matrix.neg_mul, hdQ, Matrix.diagonal_neg]) u
        (by rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]; linarith)
      exact ⟨i, by simpa using hi⟩
    have v1 := hcol (Sum.inl ⟨0, by omega⟩)
    have v2 := hcol (Sum.inr ⟨0, by omega⟩)
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
      Matrix.neg_apply, mul_one, mul_neg] at v1 v2
    rcases lt_or_gt_of_ne hφξ0 with h | h
    · exact ⟨pos _ (by rw [v2, Complex.neg_re, hcre]; linarith),
        neg _ (by rw [v1, hcre]; exact h)⟩
    · exact ⟨pos _ (by rw [v1, hcre]; exact h),
        neg _ (by rw [v2, Complex.neg_re, hcre]; linarith)⟩
  have hre : ∀ (τ : E →+* ℂ) i, (τ (d i)).re =
      ((B.emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).1 (d i)).re := fun τ i => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_fixed h2 σ hξ0 hξ (hdσ i)
    rw [← ha]
    exact re_embedding_algebraMap B.emb τ a
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E n (σ : E →+* E) G
    (fun a => hcc a) hherm hn (fun τ => by
      obtain ⟨⟨i, hi⟩, j, hj⟩ := hsignE (InfinitePlace.mk (τ.comp (algebraMap F E)))
      exact ⟨⟨_, by rw [hdiag, hre]; exact hi⟩, _, by rw [hdiag, hre]; exact hj⟩)
  refine ⟨z, hz0, ?_⟩
  rw [hform] at hz
  exact (mul_eq_zero.mp hz).resolve_left hξ0

end GlobalTheory.PlaneSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlacesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_places_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  first | exact @GlobalTheory.PlaceIso.exists_isotropic_places | exact GlobalTheory.PlaceIso.exists_isotropic_places | (intros; apply GlobalTheory.PlaceIso.exists_isotropic_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefinStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_vector_hermitian_rank_ge_three_indefinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s → Y.IsHerm σ B r s →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  first | exact @GlobalTheory.HermIso.exists_isotropic | exact GlobalTheory.HermIso.exists_isotropic | (intros; apply GlobalTheory.HermIso.exists_isotropic <;> assumption)
end

