import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexLineBundleTermTorsionFreeCharZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)

namespace GlobalTheory.CechPic

theorem intCast_mul_eq_zero_of_isIntegral {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X]
    (hc : CharZero Γ(X, ⊤)) (W : X.Opens) {m : ℤ} (hm : m ≠ 0) {c : Γ(X, W)}
    (h : (m : Γ(X, W)) * c = 0) : c = 0 := by
  by_cases hW : Nonempty W
  · have hinj := AlgebraicGeometry.map_injective_of_isIntegral X (homOfLE (le_top : W ≤ ⊤))
    have hm' : (m : Γ(X, W)) ≠ 0 := by
      intro h0
      apply hm
      have : (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (m : Γ(X, ⊤)) =
          (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom 0 := by
        rw [map_intCast, map_zero, h0]
      exact_mod_cast hinj this
    exact (mul_eq_zero.1 h).resolve_left hm'
  · have hb : W = ⊥ := eq_bot_iff.2 fun x hx => (hW ⟨⟨x, hx⟩⟩).elim
    subst hb
    have := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

theorem cechLB_X_noZSMulDivisors : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) →
    ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 →
    ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  intro X _ hc f M κ _ D n m hm x hx
  have key : ∀ (V : X.Opens) (y : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V), m • y = 0 → y = 0 := by
    intro V y hy
    refine GlobalTheory.AbLaw.SecOnR.ext (R := ℤ) (f := f) fun i => ?_
    let c : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V →+ Γ(X, V ⊓ M.U i) :=
      { toFun := fun z => GlobalTheory.AbLaw.SecOnR.coord z i
        map_zero' := GlobalTheory.AbLaw.SecOnR.coord_zero i
        map_add' := fun z w => GlobalTheory.AbLaw.SecOnR.coord_add z w i }
    have hi : c (m • y) = c 0 := congrArg c hy
    rw [map_zsmul, map_zero, zsmul_eq_mul] at hi
    exact intCast_mul_eq_zero_of_isIntegral hc _ hm hi
  funext s
  refine key _ (x s) ?_
  exact congrFun hx s

end GlobalTheory.CechPic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementCommutesTranslates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.RightTr

section Alg

variable {A : Type} [Ring A]

theorem prod_ofFn_mul_comm (R : A) : ∀ (m : ℕ) (f g : Fin m → A), (∀ i, f i * R = R * g i) →
    (List.ofFn f).prod * R = R * (List.ofFn g).prod
  | 0, _, _, _ => by simp
  | m + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_ofFn_mul_comm R m _ _ fun i => h i.succ, ← mul_assoc, h 0, mul_assoc]

theorem gelfA_mul_comm [Algebra ℂ A] {n : ℕ} (X Y : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, X a b * R = R * Y a b) (k : ℕ) :
    GlobalTheory.SmoothForms.gelfA X k * R = R * GlobalTheory.SmoothForms.gelfA Y k := by
  rw [GlobalTheory.SmoothForms.gelfA, GlobalTheory.SmoothForms.gelfA, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun idx _ => prod_ofFn_mul_comm R _ _ _ fun i => h _ _

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def rtr (h : IsCMExt F E σ) (a : GAd σ J) : Module.End ℂ (SmG σ J) where
  toFun f := ⟨fun x => f.1 (x * a), mem_SmG.2 (GlobalTheory.EisCont.CentreFinite.isSm_mul_right h (mem_SmG.1 f.2) a)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isLineOf_conj {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ}
    {γ : ℝ → GAd σ J} (hγ : IsLineOf σ J τ Z γ) (a : GAd σ J) :
    IsLineOf σ J τ (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a))
      (fun t => a⁻¹ * γ t * a) := by
  intro t
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨y, e1, e2⟩ := hγ t
  refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
  · show a⁻¹ * γ t * a = _
    rw [e1]
    refine GAd_ext σ J (fun u => ?_) fun v => by simp
    by_cases e : u = w
    · subst e; simp
    · simp [projArch_embArch_ne σ J e]
  · rw [map_mul, map_mul, e2]
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
    rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

theorem der_mul_rtr (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} {τ : EmbOver E w}
    {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD : IsDer σ J τ D) (a : GAd σ J)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    D Z * rtr h a = rtr h a *
      D (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)) := by
  have hl : ∀ Z γ, IsLineOf σ J τ Z γ → D Z * rtr h a = rtr h a *
      D (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)) := by
    intro Z γ hγ
    refine LinearMap.ext fun f => Subtype.ext ?_
    show (D Z (rtr h a f)).1 = fun x => (D _ f).1 (x * a)
    rw [hD.2 Z γ hγ, hD.2 _ _ (isLineOf_conj hγ a)]
    funext x
    simp only [lineDer, rtr, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, mul_inv_cancel_left]
  obtain ⟨γ₁, γ₂, e1, e2, e3⟩ := exists_lines h hJ τ Z
  generalize (1 / 2 : ℂ) • (Z - adj (J.map τ.1) Z) = Z₁ at e1 e3
  generalize (-Complex.I / 2 : ℂ) • (Z + adj (J.map τ.1) Z) = Z₂ at e2 e3
  subst e3
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul, map_add, map_smul,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hl _ _ e1, hl _ _ e2]

end GlobalTheory.LeviHC.RightTr

namespace GlobalTheory.LeviHC.RightTr

theorem comm_rtr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), (∀ X, D X * u = u * D X) → ∀ (a : GAd σ J) (f f' : SmG σ J),
      (f'.1 = fun x => f.1 (x * a)) → (u f').1 = fun x => (u f).1 (x * a) := by
  intro F E _ _ _ _ _ σ hcm n J hJ w τ D hD u hu hcomm a f f' hf'
  let X : Fin n → Fin n → Module.End ℂ (SmG σ J) := fun i j => D (Matrix.single i j 1)
  have hsum : ∀ M : Matrix (Fin n) (Fin n) ℂ, D M = ∑ i, ∑ j, M i j • X i j := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum, X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hgl : Formalism.REAL.GlRel X := by
    intro p q r s
    simp only [X]
    rw [← hD.1, GlobalTheory.CapFrame.single_mul_single_one, GlobalTheory.CapFrame.single_mul_single_one]
    split_ifs <;> simp [eq_comm]
  have hu' : u ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) := by
    refine Algebra.adjoin_le ?_ hu
    rintro _ ⟨M, rfl⟩
    rw [hsum]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.smul_mem _ (Algebra.subset_adjoin (R := ℂ) (s := Set.range fun p : Fin n × Fin n => X p.1 p.2) ⟨(i, j), rfl⟩) _
  obtain ⟨d, hd⟩ := GlobalTheory.SmoothForms.exists_filt hu'
  have hz := GlobalTheory.SmoothForms.central_of_filt hgl d u hd fun i j => hcomm _
  have hM : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hg : ∀ k, GlobalTheory.SmoothForms.gelfA X k * rtr hcm a = rtr hcm a * GlobalTheory.SmoothForms.gelfA X k := by
    intro k
    conv_rhs => rw [← GlobalTheory.RegSch.GelfCyc.gelfA_conj X (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹)ᵀ
      (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a))ᵀ (by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]) k]
    refine gelfA_mul_comm _ _ _ (fun i j => ?_) k
    show D (Matrix.single i j 1) * _ = _
    rw [der_mul_rtr hcm hJ hD a, hsum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hcen : u ∈ Subalgebra.centralizer ℂ {rtr hcm a} := by
    refine Algebra.adjoin_le ?_ hz
    rintro _ ⟨k, rfl⟩ g hg'
    rw [Set.mem_singleton_iff.1 hg']
    exact (hg k).symm
  have e : rtr hcm a * u = u * rtr hcm a := hcen _ rfl
  have hf : f' = rtr hcm a f := Subtype.ext hf'
  rw [hf]
  show ((u * rtr hcm a) f).1 = _
  rw [← e]
  rfl

end GlobalTheory.LeviHC.RightTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreGeneratedByGelfand
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC.MultiCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def genSet (E : Fin n → Fin n → A) : Set A := Set.range fun p : Fin n × Fin n => E p.1 p.2

theorem gelfA_mem_adjoin (E : Fin n → Fin n → A) (k : ℕ) :
    GlobalTheory.SmoothForms.gelfA E k ∈ Algebra.adjoin ℂ (genSet E) := by
  unfold GlobalTheory.SmoothForms.gelfA
  refine Subalgebra.sum_mem _ fun idx _ => Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨a, rfl⟩ := hx
  exact Algebra.subset_adjoin ⟨(_, _), rfl⟩

theorem adjoin_le_centralizer {S T : Set A} (h : ∀ x ∈ S, ∀ y ∈ T, y * x = x * y) :
    Algebra.adjoin ℂ S ≤ Subalgebra.centralizer ℂ T :=
  Algebra.adjoin_le fun x hx => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => h x hx y hy

theorem centre_of_commuting_families_sup (hRC : RelativeCentre) {ι : Type} (X : ι → Fin n → Fin n → A)
    (hX : ∀ i, Formalism.REAL.GlRel (X i)) (hc : ∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b)
    (s : Finset ι) : ∀ C : Subalgebra ℂ A, (∀ i ∈ s, C ≤ Subalgebra.centralizer ℂ (genSet (X i))) →
      ∀ z ∈ s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C,
        (∀ i ∈ s, z ∈ Subalgebra.centralizer ℂ (genSet (X i))) →
        z ∈ s.sup (fun i => Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA (X i)))) ⊔ C := by
  classical
  induction s using Finset.induction_on with
  | empty => intro C _ z hz _; simpa using hz
  | insert w s hw ih =>
    intro C hC z hz hzc
    rw [Finset.sup_insert] at hz ⊢
    have hle : s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C ≤ Subalgebra.centralizer ℂ (genSet (X w)) := by
      refine sup_le (Finset.sup_le fun i hi => adjoin_le_centralizer ?_) (hC w (Finset.mem_insert_self _ _))
      rintro x ⟨⟨a, b⟩, rfl⟩ y ⟨⟨c, d⟩, rfl⟩
      exact hc w i (fun h => hw (h ▸ hi)) c d a b
    have hB : ∀ b ∈ s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C, ∀ a c, X w a c * b = b * X w a c :=
      fun b hb a c => (Subalgebra.mem_centralizer_iff ℂ).1 (hle hb) _ ⟨(a, c), rfl⟩
    have hz' : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X w p.1 p.2) ⊔
        (s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C) := by
      rw [← sup_assoc]; exact hz
    have h1 := hRC A n (X w) (hX w) _ hB z hz' fun a c =>
      (Subalgebra.mem_centralizer_iff ℂ).1 (hzc w (Finset.mem_insert_self _ _)) _ ⟨(a, c), rfl⟩
    rw [sup_left_comm] at h1
    have hC' : ∀ i ∈ s, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA (X w))) ⊔ C ≤
        Subalgebra.centralizer ℂ (genSet (X i)) := by
      intro i hi
      refine sup_le ((Algebra.adjoin_le (Set.range_subset_iff.2 fun k => gelfA_mem_adjoin (X w) k)).trans
        (adjoin_le_centralizer ?_)) (hC i (Finset.mem_insert_of_mem hi))
      rintro x ⟨⟨a, b⟩, rfl⟩ y ⟨⟨c, d⟩, rfl⟩
      exact hc i w (fun h => hw (h ▸ hi)) c d a b
    have h2 := ih _ hC' z h1 fun i hi => hzc i (Finset.mem_insert_of_mem hi)
    rw [sup_assoc]; rwa [sup_left_comm] at h2

theorem centre_multi : RelativeCentre → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Finite ι] (n : ℕ)
    (X : ι → Fin n → Fin n → A),
    (∀ i, Formalism.REAL.GlRel (X i)) → (∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × Fin n × Fin n => X p.1 p.2.1 p.2.2),
      (∀ i a b, X i a b * z = z * X i a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × ℕ => GlobalTheory.SmoothForms.gelfA (X p.1) p.2) := by
  intro hRC A _ _ ι _ n X hX hc z hz hzc
  classical
  letI := Fintype.ofFinite ι
  have hz' : z ∈ (Finset.univ : Finset ι).sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ ⊥ := by
    rw [sup_bot_eq]
    refine (Algebra.adjoin_le ?_) hz
    rintro _ ⟨⟨i, a, b⟩, rfl⟩
    exact Finset.le_sup (f := fun i => Algebra.adjoin ℂ (genSet (X i))) (Finset.mem_univ i)
      (Algebra.subset_adjoin ⟨(a, b), rfl⟩)
  have h := centre_of_commuting_families_sup hRC X hX hc Finset.univ ⊥ (fun _ _ => bot_le) z hz' fun i _ =>
    (Subalgebra.mem_centralizer_iff ℂ).2 (by rintro _ ⟨⟨a, b⟩, rfl⟩; exact hzc i a b)
  rw [sup_bot_eq] at h
  refine (Finset.sup_le fun i _ => Algebra.adjoin_mono ?_) h
  rintro _ ⟨k, rfl⟩
  exact ⟨(i, k), rfl⟩

end GlobalTheory.LeviHC.MultiCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariantStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBall_extend_by_zero_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  first | exact @GlobalTheory.chartBall_extend_by_zero | exact GlobalTheory.chartBall_extend_by_zero | (intros; apply GlobalTheory.chartBall_extend_by_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallWeightPotentialDensityBoundsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBall_weightPotential_density_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x ∧ |phla X la (cpt X x z)| ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| ∧ |rhF X x z| ≤ (X.Ψ.card : ℝ) ∧ |Real.log (densF X x z)| ≤ (X.Ψ.card : ℝ) * r ∧ 0 < densF X x z := by
  first | exact @GlobalTheory.WeightSizes.chart_ball_sizes | exact GlobalTheory.WeightSizes.chart_ball_sizes | (intros; apply GlobalTheory.WeightSizes.chart_ball_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFirstColumnsEqGraphTimesTopBlockStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_firstColumns_eq_graph_times_topBlock : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  first | exact @GlobalTheory.ChartGraph.cols_graph | exact GlobalTheory.ChartGraph.cols_graph | (intros; apply GlobalTheory.ChartGraph.cols_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGraphCoordinatesOpNormLeOfSmall
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

theorem sum_norm_mulVec_sq_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (c : ℝ)
    (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ((m : ℝ) * n * c ^ 2) * ∑ j, ‖w j‖ ^ 2 := by
  have hi : ∀ i, ‖(M *ᵥ w) i‖ ≤ c * ∑ j, ‖w j‖ := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ j, M i j * w j‖ ≤ ∑ j, ‖M i j * w j‖ := norm_sum_le _ _
      _ ≤ ∑ j, c * ‖w j‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = c * ∑ j, ‖w j‖ := by rw [Finset.mul_sum]
  have hs : (∑ j, ‖w j‖) ^ 2 ≤ n * ∑ j, ‖w j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖w j‖)
  have hi2 : ∀ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) := fun i => by
    calc ‖(M *ᵥ w) i‖ ^ 2 ≤ (c * ∑ j, ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
      _ = c ^ 2 * (∑ j, ‖w j‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
  calc ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ∑ _i : Fin m, c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hi2 i
    _ = _ := by simp [Finset.sum_const]; ring

theorem sqrt_sum_norm_sq_eq {n : ℕ} (x : Fin n → ℂ) :
    Real.sqrt (∑ i, ‖x i‖ ^ 2) = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]

theorem norm_toLp_mulVec_le {m n r : ℕ} (hm : m ≤ r) (hn : n ≤ r) (M : Matrix (Fin m) (Fin n) ℂ)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ‖WithLp.toLp 2 (M *ᵥ w)‖ ≤ (r * c) * ‖WithLp.toLp 2 w‖ := by
  rw [← sqrt_sum_norm_sq_eq, ← sqrt_sum_norm_sq_eq]
  have hmn : (m : ℝ) * n * c ^ 2 ≤ ((r : ℝ) * c) ^ 2 := by
    have h1 : (m : ℝ) ≤ r := by exact_mod_cast hm
    have h2 : (n : ℝ) ≤ r := by exact_mod_cast hn
    have : (m : ℝ) * n ≤ (r : ℝ) * r :=
      mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg c]
  have hS := sum_norm_mulVec_sq_le M c h w
  have hB : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc Real.sqrt (∑ i, ‖(M *ᵥ w) i‖ ^ 2) ≤ Real.sqrt (((r : ℝ) * c) ^ 2 * ∑ j, ‖w j‖ ^ 2) :=
        Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_right hmn hB))
    _ = (r * c) * Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hc)]

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_coord_le (X : Data E r) (z : V (nd X)) (k : Fin (nd X)) : ‖z k‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z k

theorem norm_chartMatrixTopBlock_sub_one_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i j : Fin X.p0) :
    ‖(chartMatrixTopBlock X z τ - 1) i j‖ ≤ ‖z‖ := by
  simp only [chartMatrixTopBlock, Matrix.sub_apply, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat,
    Matrix.one_apply]
  split_ifs
  all_goals first
    | (rw [sub_zero]; exact norm_coord_le X z _)
    | (rw [sub_self, norm_zero]; exact norm_nonneg _)
    | (exfalso; simp only [Fin.lt_def, Fin.ext_iff, Fin.coe_castLE] at *; omega)

theorem norm_chartBottomLeftBlock_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r - X.p0)) (j : Fin X.p0) :
    ‖chartBottomLeftBlock X z τ i j‖ ≤ ‖z‖ := by
  simp only [chartBottomLeftBlock, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat]
  split_ifs with h1 h2
  · exact norm_coord_le X z _
  · exact absurd h2 (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · exact absurd (show Fin.castLE X.p0_le j < ⟨X.p0 + i, by have := i.isLt; have := X.p0_le; omega⟩ from
      by rw [Fin.lt_def]; simp; omega) h1

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

theorem zN_graphCoord_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  intro E _ _ _ r X z hz
  have hε : 0 ≤ ‖z‖ := norm_nonneg z
  have hrε : (r : ℝ) * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast h
      nlinarith
  apply Real.iSup_le _ (by norm_num)
  intro τ
  apply Real.sSup_le _ (by norm_num)
  rintro t ⟨v, hv, rfl⟩
  have hunit : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
  have hAv : Matrix.of (graphCoord X z τ) *ᵥ v = chartBottomLeftBlock X z τ *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    change (chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹) *ᵥ v = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  have hvw : v = (chartMatrixTopBlock X z τ)⁻¹ *ᵥ v + (chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
    abel
  have h1 := norm_toLp_mulVec_le (Nat.sub_le r X.p0) X.p0_le (chartBottomLeftBlock X z τ) ‖z‖ hε
    (norm_chartBottomLeftBlock_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h2 := norm_toLp_mulVec_le X.p0_le X.p0_le (chartMatrixTopBlock X z τ - 1) ‖z‖ hε
    (norm_chartMatrixTopBlock_sub_one_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h3 : ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)‖ ≤ ‖WithLp.toLp 2 v‖ +
      ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))‖ := by
    have hv' : WithLp.toLp 2 v = WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) +
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [← WithLp.toLp_add, ← hvw]
    have : WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) = WithLp.toLp 2 v -
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [hv', add_sub_cancel_right]
    rw [this]
    exact norm_sub_le _ _
  have hvpos : 0 < ‖WithLp.toLp 2 v‖ :=
    norm_pos_iff.mpr fun h => hv (by simpa using congrArg WithLp.ofLp h)
  rw [sqrt_sum_norm_sq_eq, sqrt_sum_norm_sq_eq, hAv, div_le_iff₀ hvpos]
  have hb := norm_nonneg (WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))
  have h4 := mul_le_mul_of_nonneg_right hrε hb
  linarith

end GlobalTheory.ChartGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibr
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefFibPrime

theorem isClosedImmersion_spMap_zmod (p : ℕ) : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))

theorem topSelf_nonneg_of_nefFib (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ)
    [Fact p.Prime] (h : ArInt.NefFib L) (Z : Scheme.{0})
    (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k))
      (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  have := isClosedImmersion_spMap_zmod p
  have : IsClosedImmersion (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
  set f := pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))) with hf
  have h1 := h Z (i ≫ f) (ZMod p) hd
  have e : topSelfIntersection (ZMod p) ((L.B.pull f).pull i) 1 = topSelfIntersection (ZMod p) (L.B.pull (i ≫ f)) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod p) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB f) i)
      (fun _ => LB.isLB_pull L.isLB (i ≫ f)) fun _ => ?_
    show pull i (pull f (cls L.B L.isLB)) = pull (i ≫ f) (cls L.B L.isLB)
    rw [← pull_comp]
  rw [e]
  exact h1

end GlobalTheory.NefFibPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulusStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbarDeriv_cutoff_normSq_bound_annulus : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.wdb_cutoff_sq_le | exact GlobalTheory.wdb_cutoff_sq_le | (intros; apply GlobalTheory.wdb_cutoff_sq_le <;> assumption)
end

