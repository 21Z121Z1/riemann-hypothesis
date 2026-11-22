import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NsubCocompact
section
noncomputable section

namespace GlobalTheory.UnipFlagCore

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Matrix
open scoped TensorProduct ENNReal

theorem mem_spanR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n r : ℕ}
    (e : Fin r → Fin n → E) (s : Set (Fin r)) (w : Fin n → R ⊗[F] E) :
    w ∈ spanR (F := F) R e s ↔
      ∃ c : Fin r → R ⊗[F] E, (∀ b, b ∉ s → c b = 0) ∧ w = ∑ b, c b • ratTup (F := F) R e b := by
  classical
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨Pi.single a 1, fun b hb => ?_, ?_⟩
      · exact Pi.single_eq_of_ne (by rintro rfl; exact hb ha) _
      · rw [Finset.sum_eq_single a]
        · simp only [Pi.single_eq_same, one_smul]; rfl
        · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
        · simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨t • c, fun b hb => by simp [hc b hb], ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hc b hb, zero_smul]; exact Submodule.zero_mem _

theorem hE_swap {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) : hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ.1 j i]; ring

theorem nsub_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F),
    P.IsStd σ J T → ∃ K : Set (Nsub (AF F) σ J P), IsCompact K ∧
      ∀ m : Nsub (AF F) σ J P, ∃ γ ∈ ratOf (K := Nsub (AF F) σ J P), ∃ k ∈ K, m = γ * k := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hσ := conj_invol hCM
  obtain ⟨h0, -, hef, -, -, -, -⟩ := hP
  have he : LinearIndependent E P.e := linearIndependent_of_dual P.e P.f fun a b => by
    rw [hE_swap hσ hJ (P.e b) (P.f a), hef]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hlin : ∀ (g : HA (AF F) σ J) (x : Fin n → AF F ⊗[F] E),
      lin (AF F) σ J g x - x = ((HA.mat _ σ J g).1 - 1) *ᵥ x := fun g x => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  obtain ⟨K, hK, hm⟩ := cocompact_of_mem_iff_adelic hσ hJ P.e he h0 (Nsub (AF F) σ J P) fun g => by
    refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun x => imp_congr Iff.rfl ?_)
    · have := mem_spanR_iff (F := F) (AF F) P.e {b | b < a} (lin (AF F) σ J g (ratV (F := F) (AF F) (P.e a)) - ratV (F := F) (AF F) (P.e a))
      rw [this, hlin]
      simp only [Set.mem_setOf_eq, not_lt]
      rfl
    · have := mem_spanR_iff (F := F) (AF F) P.e Set.univ (lin (AF F) σ J g x - x)
      rw [this, hlin]
      simp only [Set.mem_univ, not_true_eq_false, false_imp_iff, implies_true, true_and]
  refine ⟨K, hK, fun m => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hm m
  exact ⟨γ, hγ, k, hk, rfl⟩

end GlobalTheory.UnipFlagCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraints
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm

theorem pairsPar : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  intro Ca Cg cb Cw cT CT C0 C' Cl D large₂ hH hK hC' hCl hCa
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩
  obtain ⟨_, _, hvI, hv1, hf, _, hfin, _, _, _, _, hg2, hT⟩ := hH D large₂ hStd
  obtain ⟨⟨hS0, _, _⟩, _⟩ := hK
  obtain ⟨_, h2, h3, _, h5, _, h7, _, _, _, h11, h12, _, _, _, _, _, _, _, _, _, _, h23, h24, h25⟩ := hS0
  have hL : 1 < large₂.sc.L := one_lt_scale_L D large₂
  have hb2 : 2 ≤ large₂.sc.b := two_le_scale_b D large₂
  have hlb : Real.log large₂.sc.b = large₂.sc.L := log_scale_eq_L D large₂
  refine ⟨by rw [hfin, hf], (two_rank_add_two_eq_m D).symm, h24, by rw [hf]; exact h3, ?_, by rw [hlb]; exact h7,
    by rw [hf]; exact h5, hb2, by rw [hvI]; exact hv1, ?_, ?_, ?_⟩
  · rw [hf]
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := by positivity
    have : ((D.R.m ^ 5 * D.R.f : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc (D.R.m : ℝ) ^ 5 * D.R.f = 1 * ((D.R.m : ℝ) ^ 5 * D.R.f) * 1 := by ring
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f) * large₂.sc.L := by gcongr <;> linarith
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := h2
    exact_mod_cast this
  · rw [hvI]
    have hrd : 0 < D.host.rdE := pf_rd_pos D
    have hL0 : 0 < large₂.sc.L := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine h11.trans ?_
      rw [div_le_iff₀ h25]; nlinarith
    have h2v : 2 * D.host.v = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = D.host.rdE; ring
    rw [h2v]
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.2 h1
      _ = large₂.sc.b := by rw [← hlb, Real.exp_log (by linarith)]
  · have hg1 : 1 ≤ D.host.g 1 := by
      rcases Nat.eq_zero_or_pos (D.host.g 1) with h | h
      · have : gS D = 0 := by simp [gS, h]
        omega
      · exact h
    calc ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
      _ = (D.host.g 0 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by gcongr; exact_mod_cast hg1
      _ = (gS D : ℝ) := by simp [gS]
  · intro u
    refine ⟨(hT u).1.one_lt.le, ?_⟩
    have h := (h23 u).2
    calc (Tu D u : ℝ) = Tr D u := rfl
      _ ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := h
      _ ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        have : (0 : ℝ) ≤ D.R.m := by positivity
        nlinarith

end GlobalTheory.TypeAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointsOfFlagTypeSetMeasurableAndInvariantStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointsOfFlagTypeSet_measurable_and_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  first | exact @GlobalTheory.FlagMeas.typeSet_measurable_invariant | exact GlobalTheory.FlagMeas.typeSet_measurable_invariant | (intros; apply GlobalTheory.FlagMeas.typeSet_measurable_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalMatrixRepresentsAdelicPointInFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

theorem repF_of_rational : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  intro D X wt ιA hA h γ₀ y₀ hf hq y hy j
  have hs : ∀ i, ιA.symm (y.1.1 i j) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y₀ i j) := by
    intro i
    rw [hy, RingEquiv.symm_apply_eq, Matrix.map_apply, Matrix.map_apply, hA.1]
  simp_rw [hs]
  have hl : X.B.I.fmat h *ᵥ qA X wt j =
      fun k => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((γ₀ *ᵥ X.crd (qFr wt j)) k) := by
    rw [hf]
    funext k
    show (γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
      ((Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∘ X.crd (qFr wt j))) k = _
    rw [← RingHom.map_mulVec]
  rw [hl, hq j]
  funext k
  simp [qA, incl, Finset.sum_apply, map_sum, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelicStatement
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_countable_discrete_subgroup_adelic : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite := by
  first | exact @GlobalTheory.RatDiscrete.subgroup_countable_discrete | exact GlobalTheory.RatDiscrete.subgroup_countable_discrete | (intros; apply GlobalTheory.RatDiscrete.subgroup_countable_discrete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalStabiliserPointFromUnitaryFixingFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GamRat

theorem gam_rat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  intro D X u γ
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 γ.2
  obtain ⟨γ₀, hU, h1, h2⟩ := (Formalism.MainNotions.LeviCoordinates.rr_mem_GF _ _).1 hGF
  refine ⟨γ₀, hU, h1, h2, ?_⟩
  intro x hx
  have hf := (Subgroup.mem_prod.1 hH).2 x hx
  rw [h2] at hf
  have : Nontrivial (Af X.B.I.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 X.B.I.F)
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h0 : (0 : w.adicCompletion X.B.I.F) = 1 := congrArg (fun a : Af X.B.I.F => a w) h
    exact zero_ne_one h0
  funext i
  apply Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)
  calc Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x) i)
      = ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ∘ x)) i := RingHom.map_mulVec _ _ _ _
    _ = _ := congrFun hf i

end GlobalTheory.GamRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryExtendByIdentityOnFixSet
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.St

theorem col_mul_eq_mulVec {A : Type} [CommRing A] {n ι κ : Type} [Fintype n] [Fintype ι]
    (M : Matrix n ι A) (B : Matrix ι κ A) (c : κ) :
    M *ᵥ (fun i => B i c) = fun i => (M * B) i c := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem rational_unitary_extend_by_identity : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, hG', hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hU := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _ X.B.I.J
    ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) G' Q Qi hQQi hQiQ hblk hG').1 y₀ hy
  set M := Q * Matrix.fromBlocks y₀ 0 0 (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) * Qi with hM
  have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
  have hdet : IsUnit M.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := X.B.I.J⁻¹ * ((M.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J)) ?_
    rw [Matrix.mul_assoc, hU, Matrix.nonsing_inv_mul _ hJu]
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  have hMQ : M * Q = Q * Matrix.fromBlocks y₀ 0 0 1 := by
    rw [hM, Matrix.mul_assoc, hQiQ, Matrix.mul_one]
    rfl
  refine ⟨hMu.unit, ?_, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd X.B.I.E) (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J * (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J
    rw [IsUnit.unit_spec]
    exact hU
  · intro x hx
    rw [IsUnit.unit_spec]
    have key : ∀ b, M *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b) := by
      intro b
      rw [col_mul_eq_mulVec, hMQ]
      funext i
      erw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
    · have := key (Sum.inl a)
      have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext fun i => he a i
      rwa [e] at this
    · have := key (Sum.inr (Sum.inl a))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext fun i => hf a i
      rwa [e] at this
    · rw [Set.mem_singleton_iff] at hz'
      subst hz'
      have := key (Sum.inr (Sum.inr ()))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
      rwa [e] at this
  · intro j
    rw [IsUnit.unit_spec]
    have e : ∀ j, X.crd (qFr wt j) = fun i => Q i (Sum.inl j) := fun j => funext fun i => (hq j i).symm
    rw [e j, col_mul_eq_mulVec, hMQ]
    funext r
    simp only [e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    erw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.St
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingActsOnComplementFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

set_option maxHeartbeats 1000000 in

theorem unitary_fix_acts_on_complement_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw γ₀ hγ hfix
  obtain ⟨Q, Qi, G', h1, h2, hq, he, hf, hz, hG', hD⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hU : ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (starRingEnd X.B.I.E))ᵀ * X.B.I.J *
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
  have hcol : ∀ b, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ (fun i => Q i (Sum.inr b)) =
      fun i => Q i (Sum.inr b) := by
    intro b
    rcases b with a | a | ⟨⟩
    · have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext (he a)
      rw [e]; exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext (hf a)
      rw [e]; exact hfix _ (Or.inl (Or.inr ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext hz
      rw [e]; exact hfix _ (Or.inr rfl)
  obtain ⟨y, hy, hγQ⟩ := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _
    X.B.I.J _ G' Q Qi h1 h2 hD hG').2 _ hU hcol
  refine ⟨y, hy, fun j => ?_⟩
  have hQ : (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Q = Q * (Matrix.fromBlocks y (0 : Matrix (Fin (D.R.N 0)) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) (0 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin (D.R.N 0)) X.B.I.E) (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E)) := by
    rw [hγQ, Matrix.mul_assoc _ Qi Q, h2, Matrix.mul_one]
  funext i
  have e := congrFun (congrFun hQ i) (Sum.inl j)
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type] at e
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hq] at e
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingMemRationalStabiliser
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem rat_unitary_fixing_mem_gam : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  intro D X u γ₀ hγ₀ hfix
  have hs : (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)).comp (starRingEnd X.B.I.E) =
      (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)).comp (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
    ext e
    exact (PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig X.B.I e).symm
  have hm := Formalism.UG.P.bc_mem _ _ _ hs X.B.I.J γ₀ hγ₀
  let g : X.B.I.Gf := ⟨_, hm⟩
  have hg : X.B.I.fmat g = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
      (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
    Formalism.UG.P.bc_coe _ γ₀
  have hinf : (fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) ∈ Hinf X u := by
    intro v y hy
    have hP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v))
    show uMat (PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) *ᵥ
        ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)) = (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)
    rw [PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (X.B.I.φ v) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg (X.B.I.φ v) (congrFun (hfix y hy) i))
  have hfin : g ∈ Hfin X u := by
    intro y hy
    rw [hg]
    funext i
    exact (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg _ (congrFun (hfix y hy) i))
  refine ⟨⟨(fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v, g), ?_⟩, ?_, ?_⟩
  · show _ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Hinf X u).prod (Hfin X u)
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_prod.2 ⟨hinf, hfin⟩⟩
    exact ⟨γ₀, hγ₀, fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v, hg⟩
  · intro v
    exact PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v
  · exact hg

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesFrameMatrixEqRationalOfRational
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

set_option maxHeartbeats 1000000 in

theorem sTil_eq_atInf_of_rational : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ (s : X.B.I.Ginf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), (∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * γ₀.map (X.B.I.φ v) * X.B.I.P v) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → sTil X wt s = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) := by
  intro D X u wt hW s γ₀ y₀ hs hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  funext τ
  set v := X.pl.symm τ with hv
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef

  have hgram : gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [gramQ, Matrix.of_apply, rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (qFr wt a)) (X.crd (qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]

  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hdetQ : IsUnit (gramQ X wt v).det := by
    have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
    rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]; exact hdetG

  have hvec : ∀ x, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v (γ₀ *ᵥ x) := by
    intro x
    have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have hinv : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    rw [hs v]
    simp only [rv]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, φ]
  have hlin : ∀ b, rv X.B.I v (γ₀ *ᵥ X.crd (qFr wt b)) = ∑ i, φ (y₀ i b) • rvV X v (qFr wt i) := by
    intro b
    rw [hy b]
    simp only [rvV, rv]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext k
    simp [Finset.sum_apply, map_sum, map_mul, φ]
  have hM : (Matrix.of fun a b => hJ (X.B.I.ε v) (rvV X v (qFr wt a))
      (uMat (s v) *ᵥ rvV X v (qFr wt b))) = gramQ X wt v * y₀.map φ := by
    ext a b
    rw [Matrix.of_apply, show rvV X v (qFr wt b) = rv X.B.I v (X.crd (qFr wt b)) from rfl, hvec, hlin,
      Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, gramQ,
      Matrix.of_apply, Matrix.map_apply, smul_eq_mul, rvV]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hfin : y₀.map φ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) τ := by
    ext a b
    simp only [Formalism.L2.Forms.atInf, Matrix.map_apply, φ, X.φ_eq, hv, Equiv.apply_symm_apply]
    rfl
  show (gramQ X wt v)⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul, hfin]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEqStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c → c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  first | exact @GlobalTheory.UnitaryVolume.volume_unitary | exact GlobalTheory.UnitaryVolume.volume_unitary | (intros; apply GlobalTheory.UnitaryVolume.volume_unitary <;> assumption)
end

