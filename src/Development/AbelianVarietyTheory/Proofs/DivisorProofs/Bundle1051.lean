import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts

theorem relIndex_ne_zero_of_finite {G Y : Type} [AddCommGroup G] (H K : AddSubgroup G) {R : Set Y} (hR : R.Finite)
    (rel : G → Y → Prop) (h1 : ∀ k ∈ K, ∃ r ∈ R, rel k r) (h2 : ∀ k k' r, rel k r → rel k' r → k - k' ∈ H) :
    H.relIndex K ≠ 0 := by
  haveI := hR.to_subtype
  choose f hf hf' using h1
  haveI : Finite (K ⧸ H.addSubgroupOf K) := by
    refine Finite.of_injective (fun q => (⟨f _ (Quotient.out q : K).2, hf _ _⟩ : R)) fun q q' h => ?_
    have h3 : f _ (Quotient.out q : K).2 = f _ (Quotient.out q' : K).2 := congrArg Subtype.val h
    have h4 := h2 _ _ _ (hf' _ (Quotient.out q : K).2) (h3 ▸ hf' _ (Quotient.out q' : K).2)
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]
    exact h4
  exact AddSubgroup.index_ne_zero_of_finite

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem normOp_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hle : B ≤ A)
    {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

theorem normOp_comm (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hi : idx A B ≠ 0)
    (L : M →ₗ[ℂ] M) (hL : ∀ x v, L (W x v) = W x (L v)) {e : M} (he : Fixes W A e) :
    normOp lam W A B (L e) = L (normOp lam W A B e) := by
  obtain ⟨n, f, hf, hu⟩ := ((sumOp_transversal h A B hB).2.1 hi).1
  have he' : Fixes W A (L e) := fun a ha => by rw [← hL, he a ha]
  rw [normOp, normOp, ((sumOp_transversal h A B hB).1 _ he' _ f hf hu).1,
    ((sumOp_transversal h A B hB).1 _ he _ f hf hu).1, map_smul, map_sum]
  simp only [hL]

end Abstract

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idx_latF_ne_zero {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (B : Submodule (𝓞 D.host.E) (XF S T)) {N : ℕ} (hN : 0 < N) (hB : ∀ b ∈ B, N • b ∈ latF S T ΛS ΛT) :
    idx (latF S T ΛS ΛT) B ≠ 0 := by
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) N hN
  refine relIndex_ne_zero_of_finite _ _ hR
    (fun b r => ∃ u ∈ latO S T ΛS ΛT fun _ => True, N • (b : WO S T) = r + N • u) (fun b hb => h _ (hB b hb)) ?_
  rintro b b' r ⟨u, hu, h1⟩ ⟨u', hu', h2⟩
  have h3 : N • ((b : WO S T) - b') = N • (u - u') := by
    rw [nsmul_sub, nsmul_sub, h1, h2, add_sub_add_left_eq_sub]
  have h4 : (b : WO S T) - b' = u - u' := by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hN ((b : WO S T) - b'), h3, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN]
  show (b : WO S T) - b' ∈ latO S T ΛS ΛT fun _ => True
  rw [h4]
  exact sub_mem hu hu'

theorem idx_latF_eq (B : Submodule (𝓞 D.host.E) (XF S T)) :
    idx (latF S T LS LT) B = (latO S T LS LT fun _ => True).relIndex (B.toAddSubgroup.map (XF.incl S T)) :=
  AddSubgroup.relIndex_comap (latO S T LS LT fun _ => True) (XF.incl S T) B.toAddSubgroup

theorem phase_two (hA : SelfDual (gamF ψ S T) (latF S T LS LT)) (w : 𝓞 D.host.E) {u : XF S T}
    (hu : u ∈ latF S T LS LT) : phase ψ w (2 • u) = 1 := by
  have h : ψ (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u) = 1 :=
    (hA _).1 ((latF S T LS LT).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
    (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phase, h2]
  congr 2
  rw [← symplOH_add_self, ← symplOH_add_right, XF.coe_nsmul, two_nsmul]

theorem phase_half {e : AE D} (he : IsSplitIdem D e) (w : 𝓞 D.host.E) {u : XF S T} (hu : IsHalf e (u : WO S T)) :
    phase ψ w u = 1 := by
  have h : IsHalf e (intA D w • (u : WO S T)) := by
    rw [isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  rw [phase, symplOH, half_orth he h hu, mul_zero, neg_zero, AddChar.map_zero_eq_one]

theorem real_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) :
    realIdem D • mt V g = realIdem D • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => realIdem_mul_of_fin ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPart D) (infPart D).map_zero (infPart D).map_one]
  rfl

theorem fin_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) :
    (1 - realIdem D) • mt V g = (1 - realIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero]
  refine Matrix.ext fun i j => (realIdem_mul_of_real ?_).symm
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPart D) (finPart D).map_zero (finPart D).map_one]
  rfl

theorem rhoF_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) (x : XF S T) :
    rhoF S T (g, h) x = x := by
  have h1 : ∀ y : XF S T, (1 - realIdem D) • (y : WO S T) = y := fun y => by
    rw [sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]
  apply XF.ext
  rw [← h1 (rhoF S T (g, h) x), coe_rhoF, smul_actO (fin_smul_mt hg) (fin_smul_mt hh), h1]

theorem real_smul_real (u : WO S T) : (realIdem D • u).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * u i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

theorem fin_smul_fin (u : WO S T) : ((1 - realIdem D) • u).map (infPart D) = 0 := by
  funext i j
  show infPart D ((1 - realIdem D) * u i j) = 0
  rw [RingHom.map_mul, RingHom.map_sub, infPart_realIdem, RingHom.map_one, sub_self, zero_mul]

theorem off_smul_mt_place {V : HSp D} {η : AF D.host.F} {g : GA D V} (hg : SuppPl η V g) :
    (1 - algebraMap (AF D.host.F) (AE D) η) • mt V g =
      (1 - algebraMap (AF D.host.F) (AE D) η) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : algebraMap (AF D.host.F) (AE D) η • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem cA_algebraMap (η : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) η) = algebraMap (AF D.host.F) (AE D) η := by
  show η ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

theorem exists_half_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : NonSplitAt D v η) :
    ∃ a : AE D, finPart D a ∈ intAE D ∧ 2 * a = algebraMap (AF D.host.F) (AE D) η := by
  obtain ⟨⟨α, rfl, h1, h0⟩, hn⟩ := h
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [h0 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    rw [← hα] at e3
    exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, h1, h0⟩, e3⟩, e3⟩
  obtain ⟨y, hy⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
  rw [map_ofNat] at hy
  have hy' : (2 : Fv D.host.F v) * y = 1 := congrArg Subtype.val hy
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v y), ?_, ?_⟩
  · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v y, 1, rfl⟩
  · rw [two_mul, ← map_add, ← map_add, ← two_mul, hy', hα]
    rfl

theorem finPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η) :
    finPart D (algebraMap (AF D.host.F) (AE D) η) ∈ intAE D := by
  obtain ⟨β, rfl, h1, h0⟩ := h
  refine AddSubgroup.subset_closure ⟨β, fun w => ?_, 1, rfl⟩
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem smooth_theta (hψ : IsCharAF D.host.F ψ) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) (hA : SelfDual (gamF ψ S T) (latF S T ΛS ΛT))
    (hlev : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ latO S T ΛS ΛT fun _ => True, N • u ∈ U) (f : thetaSub ψ S T) :
    ∃ B : Submodule (𝓞 D.host.E) (XF S T), idx (latF S T ΛS ΛT) B ≠ 0 ∧
      ∀ a ∈ latF S T ΛS ΛT, (∀ t ∈ B, gamF ψ S T a t = 1) → opF hψ S T w a f = f := by
  have H := isHeis_opF hψ S T hw
  obtain ⟨U, hU, hf⟩ := f.2.level
  obtain ⟨N, hN, hNU⟩ := hlev U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XF S T, (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • x) = x := fun x => by
    apply XF.ext
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • (x : WO S T)) = x
    rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN2]
  refine ⟨(latF S T ΛS ΛT).comap ((2 * N) • LinearMap.id), idx_latF_ne_zero hS hT _ hN2 fun b hb => hb,
    fun a _ ha => ?_⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF S T ΛS ΛT := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • t) ∈ latF S T ΛS ΛT
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opF, hf _ (by rw [XF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end GlobalTheory.FinWeilO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothStable

theorem rep_mem_sm : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w ∈ M.sm τ, M.rep τ g w ∈ M.sm τ := by
  intro D V S M τ g hg w hw
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have e : M.sm τ = GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) :=
    Submodule.span_eq (GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
  rw [e] at hw ⊢
  exact GlobalTheory.SmVec.rep_mem (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ))
    (GlobalTheory.SmVec.isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hσ) hw hg

end GlobalTheory.SmoothStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOfZariskiSheafOpenChartsLargeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representable_of_zariski_sheaf_open_charts_large : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  first | exact @GlobalTheory.PicGlue.exists_represent_of_charts_large | exact GlobalTheory.PicGlue.exists_represent_of_charts_large | (intros; apply GlobalTheory.PicGlue.exists_represent_of_charts_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffFieldStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_character_det_values_mem_coeff_field : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChiDetValues.chiC_mem_coeff | exact GlobalTheory.ChiDetValues.chiC_mem_coeff | (intros; apply GlobalTheory.ChiDetValues.chiC_mem_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess bas wd wdb)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ENNReal

namespace GlobalTheory.ChernMA

theorem cHess_eq_hessC {D : ℕ} {h : V D → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 h (toV D z)) :
    cHess D (fun v => (h v : ℂ)) (toV D z) = hessC (h ∘ toV D) z := by
  have h₁ : fderiv ℝ (h ∘ toV D) =
      fun w => (fderiv ℝ h (toV D w)).comp (toV D).toContinuousLinearMap :=
    funext fun _ => (toV D).comp_right_fderiv
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₂ := ((hD.comp z (toV D).hasFDerivAt).clm_comp
    (hasFDerivAt_const (toV D).toContinuousLinearMap z)).fderiv
  set x := toV D z
  set H := fderiv ℝ (fderiv ℝ h) x
  have hH (a b : Fin D → ℂ) : fderiv ℝ (fderiv ℝ (h ∘ toV D)) z a b = H (toV D a) (toV D b) := by
    rw [h₁]
    erw [h₂]
    simp
  have hdiff := ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf
  set G : Fin D → V D → ℂ := fun k y => (2 : ℂ)⁻¹ *
    ((fderiv ℝ h y (bas D k) : ℂ) + Complex.I * (fderiv ℝ h y (Complex.I • bas D k) : ℂ))
  have hwdb : ∀ k, wdb D k (fun y => (h y : ℂ)) =ᶠ[𝓝 x] G k := by
    intro k
    filter_upwards [hdiff] with y hy
    simp only [wdb, G, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy]
    ring
  have hGd : ∀ k e, fderiv ℝ (G k) x e =
      ((H e (bas D k) : ℂ) + Complex.I * (H e (Complex.I • bas D k) : ℂ)) / 2 := by
    intro k e
    have ha : ∀ b : V D, HasFDerivAt (fun y => ((fderiv ℝ h y b : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ h x).comp (0 : V D →L[ℝ] V D) + H.flip b)) x :=
      fun b => Complex.ofRealCLM.hasFDerivAt.comp x (hD.clm_apply (hasFDerivAt_const b x))
    have hG : HasFDerivAt (G k) _ x :=
      ((ha (bas D k)).add ((ha (Complex.I • bas D k)).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    rw [hG.fderiv]
    simp
    ring
  have e₁ (a : Fin D) : toV D (Pi.single a 1) = bas D a := rfl
  have e₂ (a : Fin D) : toV D (Complex.I • Pi.single a 1) = Complex.I • bas D a := rfl
  ext j l
  rw [cHess, Matrix.of_apply, wd, (hwdb l).fderiv_eq, hGd, hGd]
  simp only [hessC, hH, e₁, e₂]
  push_cast
  linear_combination (-(H (Complex.I • bas D j) (Complex.I • bas D l) : ℂ) / 4) * Complex.I_mul_I

theorem map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : Measure α}
    {s : α → β} (hs : AEMeasurable s m) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (m.map s).withDensity g = (m.withDensity (g ∘ s)).map s := by
  ext T hT
  rw [Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply _ hT, ← lintegral_indicator hT,
    lintegral_map' (hg.indicator hT).aemeasurable hs,
    withDensity_apply₀ _ (hs.nullMeasurableSet_preimage hT),
    ← lintegral_indicator₀ (hs.nullMeasurableSet_preimage hT)]
  rfl

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B : LB Y} {φ : Weight p σ B} {A : FinHolAtlas D (CxPts p σ)}

theorem locDens_eq (h : φ.IsCInf) {c : AlgChart p σ D} {j : Fin A.n} (hc : A.chart j = c.finChart)
    {z : Fin D → ℂ} (hz : z ∈ c.finChart.target) :
    locDens A (fun _ => φ.locPot) j z = c.chernDens φ (c.finChart.symm z) := by
  have hy := c.finChart.map_target hz
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hs := h.contDiffAt c hy (mem_pick φ.isLB _)
  rw [hr] at hs
  have e : (fun y' => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y')) = fun v => 2⁻¹ *
      ((fun v => φ.φ (pick φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) v :=
    funext fun _ => div_eq_inv_mul _ _
  rw [locDens, hc, maDens, ReciprocityTheory.AnForm.A.mdisc_const, e, hessC_const_mul', AlgChart.chernDens,
    AlgChart.hess, hr, cHess_eq_hessC hs, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul, div_pow, inv_pow]
  field_simp

variable [SecondCountableTopology (CxPts p σ)]

theorem restrict_chernPart (h : φ.IsCInf) (ε : ℤˣ) (c : AlgChart p σ D) :
    (φ.chernPart D ε).restrict c.finChart.source = ((volume.restrict c.finChart.target).withDensity
      fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z))).map c.finChart.symm := by
  ext T hT
  have ht := c.finChart.open_target.measurableSet
  have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable ht
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c
      (hT.inter c.finChart.open_source.measurableSet) inter_subset_right,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', Measure.restrict_restrict' ht, inter_comm, AlgChart.finChart_source,
    c.e.image_source_inter_eq', ← hp.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), inter_comm]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]

omit [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] in

theorem chernPart_eq_sum (h : φ.IsCInf) (hA : IsAlgAtlas A) (P : ChartPartition A) (ε : ℤˣ) :
    φ.chernPart D ε = ∑ j, chartPartMeasure A P (fun _ => φ.locPot) (ε : ℤ) j := by
  have hm (j) : Measurable fun y => ENNReal.ofReal (P.χ j y) :=
    ENNReal.measurable_ofReal.comp (continuousOn_univ.1
      (((hA.smooth_iff hA.anRead).1 (P.smooth j)).continuousOn isOpen_univ)).measurable
  have hpot := ((Weight.isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA
  have key (j) : chartPartMeasure A P (fun _ => φ.locPot) (ε : ℤ) j =
      (φ.chernPart D ε).withDensity fun y => ENNReal.ofReal (P.χ j y) := by
    obtain ⟨c, hc⟩ := hA j
    have ht := c.finChart.open_target.measurableSet
    have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
      c.finChart.continuousOn_symm.aemeasurable ht
    have e : (fun y => ENNReal.ofReal (P.χ j y)) =
        c.finChart.source.indicator fun y => ENNReal.ofReal (P.χ j y) := by
      refine (indicator_eq_self.2 fun y hy => hc ▸ P.tsupport_subset j (subset_tsupport _ ?_)).symm
      exact fun h0 => hy (by simp [h0])
    have hd : AEMeasurable (fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z)))
        (volume.restrict c.finChart.target) := by
      have := locDensCont A _ (fun _ => hpot) j
      rw [hc] at this
      exact (((this.congr fun z hz => (locDens_eq h hc hz).symm).aemeasurable ht).const_mul
        _).ennreal_ofReal
    rw [e, withDensity_indicator c.finChart.open_source.measurableSet, restrict_chernPart h,
      map_withDensity (hs.mono_ac (withDensity_absolutelyContinuous _ _)) (hm j),
      ← withDensity_mul₀ hd ((hm j).comp_aemeasurable hs), chartPartMeasure]
    simp only [hc]
    refine congrArg _ (withDensity_congr_ae (ae_restrict_of_forall_mem ht fun z hz => ?_))
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [locDens_eq h hc hz, mul_left_comm, ENNReal.ofReal_mul (P.nonneg _ _), mul_comm]
  ext T hT
  simp only [key, Measure.coe_finsetSum, Finset.sum_apply, withDensity_apply _ hT]
  rw [← lintegral_finsetSum _ fun j _ => hm j, ← setLIntegral_one]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => P.nonneg j y, P.sum_eq_one, ENNReal.ofReal_one]

theorem chernInt_eq_mInt (h : φ.IsCInf) (hA : IsAlgAtlas A) {f : CxPts p σ → ℝ}
    (hf : Continuous f) : φ.chernInt D univ f = mInt A (fun _ => φ.locPot) f := by
  have hΦ : ∀ _ : Fin D, IsPotential A φ.locPot := fun _ =>
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA
  have hi := mIntegrableCont A _ hΦ f hf
  set P := (existsPartition A).some
  have h1 := fun s j => integral_chartPartMeasure A P _ hΦ s j f hf.measurable hi
  have h2 (s : ℝ) (j) : IntegrableOn (fun y => f ((A.chart j).symm y) * max (s * (P.χ j
      ((A.chart j).symm y) * locDens A (fun _ => φ.locPot) j y)) 0) (A.chart j).target := by
    obtain ⟨hK, hKT, h0⟩ := chart_weight_compact A P (fun _ => φ.locPot) j
    have hχ : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target :=
      (P.smooth j j).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩
    refine ((((hf.comp_continuousOn (A.chart j).continuousOn_symm).mul ((continuousOn_const.mul
      (hχ.mul (locDensCont A _ hΦ j))).sup continuousOn_const)).mono hKT).integrableOn_compact
      hK).of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet fun y hy => ?_
    simp [h0 y hy.1 hy.2]
  rw [Weight.chernInt, Measure.restrict_univ, Measure.restrict_univ, chernPart_eq_sum h hA P,
    chernPart_eq_sum h hA P, integral_finsetSum_measure fun j _ => (h1 _ j).1,
    integral_finsetSum_measure fun j _ => (h1 _ j).1, ← Finset.sum_sub_distrib, mInt,
    dif_pos (existsPartition A), integralWith]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h1 _ j).2, (h1 _ j).2, ← integral_sub (h2 _ j) (h2 _ j)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
  rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  ring

end GlobalTheory.ChernMA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ringHom_eq_on_adjoin_simple {E : Type} [Field E] [Algebra ℚ E] (f g : E →+* ℂ) (s : E) (h : f s = g s) (x : E)
    (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) : f x = g x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem overK_iff_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ) :
    OverK σ ↔ σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) :=
  ⟨fun h => h _ (IntermediateField.mem_adjoin_simple_self ℚ D.host.sqrtMinusD),
    fun h x hx => ringHom_eq_on_adjoin_simple (σ.comp D.embE) (D.what₂.embLL.comp D.embE) D.host.sqrtMinusD h x hx⟩

theorem overK_iff_good_of_pins {D : D7} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (ha : AlgTie T) (hp : T.Q.Pins)
    (σ : D.what₂.LL →+* ℂ) : OverK σ ↔ GoodEmb T.Q.c (res T σ) := by
  have e0 := res_embLL T ha hp.2.2.1
  have h1 : D.what₂.embLL (D.embE D.host.sqrtMinusD) = T.Q.H.rt0 :=
    (RingHom.congr_fun D.embE_φ₀ D.host.sqrtMinusD).trans hp.1.2.2.1.symm
  have h2 : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.toCore.good_σ₀
  have hx : D.embE D.host.sqrtMinusD = algebraMap T.Q.c.F D.what₂.LL
      (IntermediateField.inclusion T.Q.c.le (ReciprocityTheory.ChartRestriction.G.Geo.Tor.baseKA T.Q.l).ρ) :=
    D.what₂.embLL.injective (h1.trans (Eq.symm h2))
  refine (overK_iff_sqrt σ).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg σ hx).symm.trans (h.trans h1)
  · exact (congrArg σ hx).trans (Eq.trans h h1.symm)

theorem overK_iff_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ) :=
  fun T _ _ _ _ _ _ fw _ σ => overK_iff_good_of_pins T fw.alg_eq fw.laws.pins σ

end GlobalTheory.GalLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjecStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_adelicProdUnramifiedEmbedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  first | (exact @GlobalTheory.LKMid.pair_embedding_injective) | (exact GlobalTheory.LKMid.pair_embedding_injective) | (intros; apply GlobalTheory.LKMid.pair_embedding_injective  <;> assumption)
end

