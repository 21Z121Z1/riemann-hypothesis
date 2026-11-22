import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsUnitaryCharacterEqDetPower
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedLatticeReframeHomMatrixIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Lat

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem gram_reS_eq : (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  refine Matrix.ext fun (i j : Fin S.rank) => ?_
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b k).symm
  show S.hT (b i) (b j) = ∑ k, (∑ l, star (frP S b l i) * S.gram l k) * frP S b k j
  rw [hb i, hb j]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    HSpace.gram, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_frameMatrix_mulVec_smul (s' : Fin S.rank → D.host.E) :
    ∑ k, (frP S b *ᵥ s') k • S.frame k = ∑ a, s' a • b a := by
  have hb : ∀ a, b a = ∑ l, frP S b l a • S.frame l := fun a =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b a).symm
  simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem mem_L0c_iff_mem_intVec_of_span_frame (s' : Fin S.rank → D.host.E) : s' ∈ L0c D (reS S b) ↔ frP S b *ᵥ s' ∈ L0c D S := by
  show ∑ a, s' a • b a ∈ S.L0 ↔ ∑ k, (frP S b *ᵥ s') k • S.frame k ∈ S.L0
  rw [sum_frameMatrix_mulVec_smul]

theorem reW_gen (X : AF D.host.F) (a : D.host.E) (t : Fin T.rank → D.host.E) (s' : Fin S.rank → D.host.E) :
    reW S T b (Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
      Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j) := by
  have h0 : ∀ G' : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G' = (frP S b)ᴴ * S.gram * frP S b →
      (star s' ᵥ* G') ᵥ* frPinv S b = star (frP S b *ᵥ s') ᵥ* S.gram := by
    rintro G' rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, frameMatrix_mul_frameMatrixInv, Matrix.mul_one,
      Matrix.star_mulVec, Matrix.vecMul_vecMul]
  have h1 := h0 (reS S b).gram (gram_reS_eq S b)
  have hv : ∀ j, ∑ c, (∑ k, star (s' k) * (reS S b).gram k c) * frPinv S b c j =
      ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j := fun j => congrFun h1 j
  ext i j
  change ∑ c, X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k c) * incA D (frPinv S b c j) = _
  rw [Matrix.of_apply, ← hv j, Finset.mul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  show X ⊗ₜ[D.host.F] _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]

theorem map_latO (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) :
    (latO (reS S b) T (L0c D (reS S b)) LT P).map (reWHom S T b) = latO S T (L0c D S) LT P := by
  unfold latO
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨w', ⟨α, hα, hP, a, ha, s', hs', t, ht, rfl⟩, rfl⟩
    exact ⟨α, hα, hP, a, ha, _, (mem_L0c_iff_mem_intVec_of_span_frame S b s').1 hs', t, ht, reW_gen S T b _ a t s'⟩
  · rintro ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    have hs' : frP S b *ᵥ (frPinv S b *ᵥ s) = s := by
      rw [Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    refine ⟨_, ⟨α, hα, hP, a, ha, frPinv S b *ᵥ s, (mem_L0c_iff_mem_intVec_of_span_frame S b _).2 (hs'.symm ▸ hs), t, ht, rfl⟩, ?_⟩
    have key : ∀ s' s : Fin S.rank → D.host.E, frP S b *ᵥ s' = s →
        reW S T b (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
        Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
      rintro s' s rfl
      exact reW_gen S T b _ a t s'
    exact key _ _ hs'

end GlobalTheory.AdSpan.ReVec.Lat

open GlobalTheory.AdSpan.ReVec.Lat in

theorem GlobalTheory.AdSpan.ReVec.latO_reW_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T),
    u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔
      reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  intro D S T b LT u
  rw [← map_latO S T b LT]
  exact (AddSubgroup.mem_map_iff_mem (f := reWHom S T b) (reW_bijective S T b).1).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemPrincGLOfCong
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}
theorem conj_back {G : Type*} [Group G] (b g : G) : b⁻¹ * (b * g * b⁻¹) * b = g := by group

theorem mem_princGL_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {I : Ideal (𝓞 E)} (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = Ideal.absNorm I • z) : x ∈ GlobalTheory.Grid.princGL β I := by
  obtain ⟨y, rfl⟩ := h2
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, rfl, fun i j => ?_⟩
  have e2 : β⁻¹ * frGL β y * β = intGL F E n y := conj_back β _
  rw [e2] at e
  have e3 := congrFun (congrFun e i) j
  have hmem : ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) ∈ idS F I := by
    rw [← map_natCast (oToS F E)]
    exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  have e4 : ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) i j = ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) * ⟨z i j, hz i j⟩ := by
    apply Subtype.ext
    refine Eq.trans ?_ (e3.trans ?_)
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · simp [nsmul_eq_mul]
  rw [e4]
  exact Ideal.mul_mem_right _ _ hmem

theorem princ_isOpen (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsOpen (((N.princ I).comap (Lev.finE N.V) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig N.V.gram
  have hf : Continuous (finHom N.V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  have hN : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ N.V N.β ∅,
    GlobalTheory.FunObj.eventually_cong_mat N.β hN hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
  exact ⟨h1, mem_princGL_of_cong h2 hz e⟩

theorem princ_isCompact (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsCompact ((Lev.levA N.V (N.princ I) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact N.V N.β
  refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC N.V).inter
    (Subgroup.isClosed_of_isOpen _ (princ_isOpen N hI))) fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  exact hCm k hk1 (GlobalTheory.Grid.princGL_top N.β ▸ GlobalTheory.Grid.princGL_mono N.β le_top hk2.2)

theorem exists_isMeasFD (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))) : ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕 := by
  choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K ho hc (fun _ m => Lev.IsMinf m) (fun _ => m _ _)
    (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem exists_measDat (N : GlobalTheory.Grid.Node D) (hs : N.V.SigOK) (df : Prop) (hdf : df → ∀ τ, (N.V.sig τ).2 = 0)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : ∃ m : N.MeasDat, m.Is df (N.princ I) := by
  have ho := princ_isOpen N hI
  have hc := princ_isCompact N hI
  by_cases h : df
  · obtain ⟨μ, 𝓕, e⟩ := GlobalTheory.FunObj.exists_meas N.V hs (hdf h) (N.princ I) ⟨ho, hc⟩
    rw [if_pos rfl] at e
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun _ => e, fun hn => absurd h hn⟩⟩
  · obtain ⟨μ, 𝓕, e⟩ := exists_isMeasFD N.V hs _ ho hc
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun h' => absurd h' h, fun _ => e⟩⟩

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem exists_isMeas (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces) :
    ∃ m00 mV mP mX, (withMeas G m00 mV mP mX).IsMeas := by
  have hlvl : G.lvl R ≠ ⊥ := G.toPlaceDat.ideal_ne_bot R.Pg
  have htop : (⊤ : Ideal (𝓞 D.host.E)) ≠ ⊥ := top_ne_bot
  obtain ⟨m00, h00⟩ := exists_measDat (G.V 0 0) (D.sp.Y_sig 0) False (fun h => h.elim) hlvl
  have hV : ∀ i j, ∃ m : (G.nV i j).MeasDat, i + 1 ≤ D.R.m → j ≤ D.R.m →
      m.Is (if j = 0 then False else D.R.m - 1 ≤ j) ((G.nV i j).princ (if j = 0 then G.lvl R else ⊤)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j ≤ D.R.m
    · have hN := hS.vert i j h.1 h.2
      obtain ⟨m, hm⟩ := exists_measDat (G.nV i j) hN.sigOK (if j = 0 then False else D.R.m - 1 ≤ j)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - j) / 2 = 0
          by_cases hj : j = 0
          · rw [if_pos hj] at hd; exact hd.elim
          · rw [if_neg hj] at hd; omega)
        (I := if j = 0 then G.lvl R else ⊤) (by split_ifs; exacts [hlvl, htop])
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hP : ∀ i, ∃ m : (G.P i).MeasDat, i ≤ D.R.m → m.Is (i = D.R.m) ((G.P i).princ (G.lvl R)) := by
    intro i
    by_cases h : i ≤ D.R.m
    · have hN := hS.P i h
      obtain ⟨m, hm⟩ := exists_measDat (G.P i) hN.sigOK (i = D.R.m)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - i + 1) / 2 = 0
          omega) hlvl
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  have hX : ∀ j, ∃ m : (G.nX j).MeasDat, j + 1 ≤ D.R.m → m.Is True ((G.nX j).princ ⊤) := by
    intro j
    by_cases h : j + 1 ≤ D.R.m
    · have hN := hS.X j h
      obtain ⟨m, hm⟩ := exists_measDat (G.nX j) hN.sigOK True
        (fun _ τ => by
          rw [hN.sig τ]) htop
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  choose mV hmV using hV
  choose mP hmP using hP
  choose mX hmX using hX
  refine ⟨m00, mV, mP, mX, ⟨fun i hi => ?_, fun i j hi hj => ?_, fun i hi => hmP i hi, fun j hj => hmX j hj⟩⟩
  · cases i with
    | zero => exact h00
    | succ i =>
      have := hmV i 0 hi (Nat.zero_le _)
      rw [if_pos rfl, if_pos rfl] at this
      exact this
  · have := hmV i (j + 1) hi hj
    rw [if_neg (Nat.succ_ne_zero j), if_neg (Nat.succ_ne_zero j)] at this
    exact this

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecSubMemLatticeCompletionOfLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevExt

variable {D : D7}

theorem intAf_mul {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) :
    a * b ∈ intAf D.host.F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem smul_mem_hatV {k : ℕ} (L : Lt D.host.E k) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    ∀ w ∈ hatV L, a • w ∈ hatV L := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨a * a', intAf_mul ha ha', x, hx, ?_⟩
    funext i
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem mulVec_sub_mem_hatV : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    (∀ x ∈ L, m *ᵥ toAf x - toAf x ∈ hatV L') → ∀ u ∈ hatV L, m *ᵥ u - u ∈ hatV L' := by
  intro D k L L' m h u hu
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hy : (fun i => a ⊗ₜ[D.host.F] x i) = a • toAf (D := D) x := by
      funext i
      simp [toAf, TensorProduct.smul_tmul', smul_eq_mul]
    rw [hy, Matrix.mulVec_smul, ← smul_sub]
    exact smul_mem_hatV L' ha _ (h x hx)
  | zero => simp
  | add y z _ _ hy hz =>
    have : m *ᵥ (y + z) - (y + z) = (m *ᵥ y - y) + (m *ᵥ z - z) := by
      rw [Matrix.mulVec_add]; abel
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : m *ᵥ (-y) - (-y) = -(m *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [this]; exact neg_mem hy

end GlobalTheory.LevExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCovers
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem nonempty_fockData_of_covers :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q)
      (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) :=
  GlobalTheory.T.nonempty_fockModel_unitary_dual_pair

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInductionStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicProductTwoReps_equiv_two_block_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) := by
  first | exact @GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | exact GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | (intros; apply GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_levelIdempotentProduct_and_centralProduct : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  first | exact @GlobalTheory.LevRange.ranges | exact GlobalTheory.LevRange.ranges | (intros; apply GlobalTheory.LevRange.ranges <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDefStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoint_acts_linearly_on_multiplicity_values_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  first | exact @GlobalTheory.RealAct.real_acts | exact GlobalTheory.RealAct.real_acts | (intros; apply GlobalTheory.RealAct.real_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsUnitaryCharacterEqDetPowerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_unitaryCharacter_eq_detPower : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → V.SigOK → ∀ z : GA D V → ℂ, (∀ a ∈ GinfC V, ∀ a' ∈ GinfC V, z (a * a') = z a * z a') → (∀ a ∈ GinfC V, ‖z a‖ = 1) → ContinuousOn z (GinfC V : Set (GA D V)) → ∃ m : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, z a = detPow θ V m a := by
  first | exact @GlobalTheory.AdSpan.char_eq_detPow | exact GlobalTheory.AdSpan.char_eq_detPow | (intros; apply GlobalTheory.AdSpan.char_eq_detPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConjStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r a b : ℕ}
    (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  first | exact @GlobalTheory.RadRedLift.red_lift | exact GlobalTheory.RadRedLift.red_lift | (intros; apply GlobalTheory.RadRedLift.red_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecGL w ρ x B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | exact GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | (intros; apply GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSphericalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_parameter_of_spherical : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), GlobalTheory.LGrp.IsSpherical ρ (KGL w n) → (∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ x ∈ fixed ρ (KGL w n), heckeVec ρ (KGL w n) h x = c • x) → ∃ B, HasSatGL w ρ B := by
  first | exact @GlobalTheory.LFun.ExSatGL.exists_hasSatGL | exact GlobalTheory.LFun.ExSatGL.exists_hasSatGL | (intros; apply GlobalTheory.LFun.ExSatGL.exists_hasSatGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalOfAFormBForm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma pos_of_isLval {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {c : Eig D} {z : ℝ} (h : IsLval R i t c z) : 0 < z := by
  obtain ⟨_, _, hL⟩ := h
  exact hL.2.1

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {p q r : Prop} (f : p → q) (k₁ : ¬p → r) (k₂ : q → r) : r := by
  by_cases hp : p
  · exact k₂ (f hp)
  · exact k₁ hp

theorem scal_of_aForm_bForm {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (SF)
    (hA : AForm R SF) (hB : BForm R SF) (hM : MatchUp R SF) : Scal R SF := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨κ₀, hκ₀, hB⟩ := hB
  have hPa : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i

  have hA' : ∀ i t c, ∃ l : ℝ, 0 < l ∧
      (∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((l : ℝ) : ℂ) • x) ∧
      ((∃ z, IsLval R i t c z ∧ l = a i * z) ∨ ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0) := by
    intro i t c
    refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hA i t c) (fun h => ?_) (fun hq => ?_)
    · have h0 : ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0 := by
        intro x hx
        by_contra hne
        exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
      refine ⟨1, one_pos, fun x hx => ?_, Or.inr h0⟩
      rw [h0 x hx]
      simp only [map_zero, smul_zero]
    · obtain ⟨z, hz, hx⟩ := hq
      exact ⟨a i * z, mul_pos (ha i) (pos_of_isLval hz), hx, Or.inl ⟨z, hz, rfl⟩⟩
  choose lam hlpos hlW hlz using hA'
  refine ⟨lam, κ₀ / (∏ i, a i), div_pos hκ₀ hPa, hlpos, hlW, ?_⟩
  intro t c x hx
  refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hM c) (fun h => ?_) (fun hW => ?_)
  ·
    have hx0 : x = 0 := by
      by_contra hne
      exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
    rw [hx0]
    simp only [map_zero, smul_zero]
  ·
    have hz' : ∀ i, ∃ z, IsLval R i t c z ∧ lam i t c = a i * z := fun i =>
      (hlz i t c).resolve_right fun h0 => hW i ((Submodule.eq_bot_iff _).mpr h0)
    choose z hz hlz' using hz'
    have key : κ₀ / (∏ i, a i) * ∏ i, lam i t c = κ₀ * ∏ i, z i := by
      rw [Finset.prod_congr rfl fun i _ => hlz' i, Finset.prod_mul_distrib, ← mul_assoc,
        div_mul_cancel₀ κ₀ hPa.ne']
    rw [key]
    exact hB t c z hz x hx

end GlobalTheory.LiftRows

end
end

