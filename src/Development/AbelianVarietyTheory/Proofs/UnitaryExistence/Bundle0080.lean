import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.EtaleProductPrimes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicElementLattice_full_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  first | exact @GlobalTheory.Member.latG_lattice_and_completion | exact GlobalTheory.Member.latG_lattice_and_completion | (intros; apply GlobalTheory.Member.latG_lattice_and_completion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Arch

theorem unit_iff {E : Type} [CommRing E] {n : Type} [Fintype n] (τ : E →+* ℂ) (G : Matrix n n E) (u : Matrix n n ℂ) :
    uᵀ * (-Gᵀ).map τ * u.map (starRingEnd ℂ) = (-Gᵀ).map τ ↔ uᴴ * G.map τ * u = G.map τ := by
  have e : (-Gᵀ).map τ = -(G.map τ)ᵀ := by
    ext a b; simp
  have e2 : u.map (starRingEnd ℂ) = (uᴴ)ᵀ := by
    ext a b; simp
  rw [e, e2, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.transpose_mul]
  exact Matrix.transpose_injective.eq_iff

theorem form_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) :
    (Formalism.UG.cT s M * J * M).map φ = (M.map φ)ᴴ * J.map φ * M.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  exact h _

theorem mat_ext {A : Type} [CommRing A] {n ι : Type} (θ : ι → (A →+* ℂ))
    (hθ : Function.Injective fun (z : A) (i : ι) => θ i z) {M N : Matrix n n A}
    (h : ∀ i, M.map (θ i) = N.map (θ i)) : M = N :=
  Matrix.ext fun a b => hθ (funext fun i => congrFun (congrFun (h i) a) b)

theorem exists_lift {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (θ : ι → (A →+* ℂ)) (hθ : Function.Bijective fun (z : A) (i : ι) => θ i z)
    (hs : ∀ i z, θ i (s z) = starRingEnd ℂ (θ i z)) (J : Matrix n n A) (hJ : ∀ i, (J.map (θ i)).det ≠ 0)
    (u : ι → Matrix n n ℂ) (hu : ∀ i, (u i)ᴴ * J.map (θ i) * u i = J.map (θ i)) :
    ∃ g : GL n A, g ∈ Formalism.UG.UJ s J ∧ ∀ i, g.1.map (θ i) = u i := by
  have lift : ∀ w : ι → Matrix n n ℂ, ∃ M : Matrix n n A, ∀ i, M.map (θ i) = w i := by
    intro w
    choose M hM using fun a b => hθ.2 fun i => w i a b
    exact ⟨Matrix.of M, fun i => Matrix.ext fun a b => congrFun (hM a b) i⟩
  have hd : ∀ i, IsUnit (u i).det := by
    intro i
    refine IsUnit.mk0 _ fun h0 => hJ i ?_
    rw [← hu i, Matrix.det_mul, h0, mul_zero]
  obtain ⟨M, hM⟩ := lift u
  obtain ⟨N, hN⟩ := lift fun i => (u i)⁻¹
  refine ⟨⟨M, N, mat_ext θ hθ.1 fun i => ?_, mat_ext θ hθ.1 fun i => ?_⟩, mat_ext θ hθ.1 fun i => ?_, hM⟩
  · rw [Matrix.map_mul, hM, hN, Matrix.mul_nonsing_inv _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, hM, hN, Matrix.nonsing_inv_mul _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [form_map s (θ i) (hs i), hM, hu]

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem continuous_inf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) : AF F ⊗[F] E → Ainf F ⊗[F] E) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  have : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(fstA F).toRingHom] Ainf F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((fstA F).toRingHom : AF F → Ainf F) := continuous_fst
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem inf_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J := by
  let π : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hπ : ∀ z, π (sigR (AF F) σ z) = sigR (Ainf F) σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a x => rfl
  have hg' : Formalism.UG.cT (sigR (AF F) σ) g.1 * JR (AF F) J * g.1 = JR (AF F) J := hg
  have hJ : (JR (F := F) (AF F) J).map π = JR (Ainf F) J := rfl
  have hc : (Formalism.UG.cT (sigR (AF F) σ) g.1).map π = Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) :=
    Matrix.ext fun a b => hπ _
  change Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) * JR (Ainf F) J * g.1.map π = JR (Ainf F) J
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

variable {D : D7}

theorem JR_map (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map θ = V.gram.map τ :=
  Matrix.ext fun _ _ => h.1 _

theorem archM_of_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : infHom V k = 1) : archM V θ k = 1 := by
  rw [archM, hk, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_archM (V : HSp D) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (hθ : Continuous θ) :
    Continuous fun h => archM V θ h := by
  have h1 : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  exact (h1.matrix_map (continuous_inf D.host.F D.host.E)).matrix_map hθ

theorem archM_spec : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  intro D V θ hθ
  obtain ⟨hc, hs, hb⟩ := (GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType D).2 θ hθ
  refine ⟨fun τ => ⟨archM_of_one V _ (map_one _), fun h h' => ?_, fun k hk => archM_of_one V _ hk,
    continuous_archM V (hc τ), fun h => ?_⟩, fun h hh => ?_, fun u hu => ?_⟩
  · rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
  · have hm : Formalism.UG.cT (sigR (Ainf D.host.F) D.sp.cm.sig) (infHom V h).1 * JR (Ainf D.host.F) V.gram * (infHom V h).1 =
        JR (Ainf D.host.F) V.gram := inf_mem D.sp.cm.sig V.gram (matHom V h) h.2
    rw [unit_iff, ← JR_map V (hθ τ), archM, ← form_map _ _ (hs τ), hm]
  · refine Units.ext (mat_ext _ hb.1 fun τ => ?_)
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hh τ.1 τ.2
  · obtain ⟨g, hg, hgu⟩ := exists_lift (sigR (Ainf D.host.F) D.sp.cm.sig) _ hb (fun τ => hs τ.1)
      (JR (Ainf D.host.F) V.gram) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        have : (V.gram.map τ.1).det = τ.1 V.gram.det := (τ.1.map_det V.gram).symm
        rw [this]
        exact (map_ne_zero τ.1).2 (gram_det_ne_zero V)) (fun τ => u τ.1) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        exact (unit_iff _ _ _).1 (hu τ.1 τ.2))
    obtain ⟨a, ha, hag⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.2 g hg
    refine ⟨a, ha, fun τ hτ => ?_⟩
    rw [archM, hag]
    exact hgu ⟨τ, hτ⟩

end GlobalTheory.Member.Arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EtaProductOfTorusBound
section
noncomputable section

namespace GlobalTheory.EtaProdCompare

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductPrimes GlobalTheory.TorusFrameRigid

section Num

variable (E : Type) [Field E] [NumberField E]

def gap (r m r1 : ℕ) : ℝ := A E r m r1 * (1 + Real.log (2 * Real.pi - 1))

end Num

section Torus

variable {E : Type} [Field E] [NumberField E]

def FixBound (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (r1 Nc nt i : ℕ) (y : ℝ) : Prop :=
  ∃ (c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ) (a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin X.r → Vsp X.dim),
    (∀ g t, |c g t| ≤ Nc) ∧ (∀ g t, TrOK X r1 (a g t)) ∧ y ≤ ∏ g, ∑ t, |(c g t : ℝ)| * thRat X s (a g t)

variable {X : PT E} {s : (Fin 1 → Vsp X.dim) → ℂ} {r1 i : ℕ} {y : ℝ}

theorem FixBound.prodBound {Nc nt : ℕ} {N : ℝ} (hN : (Nc : ℝ) ≤ N) (hn : nt ≤ r1 ^ (2 * PT.f E * X.r ^ 2))
    (h : FixBound X s r1 Nc nt i y) : ProdBound X s r1 N i y := by
  obtain ⟨c, a, hc, ha, hy⟩ := h
  exact ⟨fun _ => nt, c, a, fun _ => hn, fun g t => le_trans (by exact_mod_cast hc g t) hN, ha, hy⟩

variable {Y : PT E} {ψ : Vsp X.dim ≃ₗ[ℝ] Vsp Y.dim}

variable [IsCMField E] {r : ℕ} {Z : FD.Data E r} {x : FD.Frame Z.Ψ r}

theorem isTorusAt (A : TorusAt Z x) : IsTorusAt Z x A.T := TorusAtDataPf.torusAtIs_holds E r Z x A

end Torus

section Record

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) {j i : ℕ} (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def nTerms (D : D7) : ℕ := 5 ^ (2 * PT.f D.host.E * D.R.r ^ 2)

def EtProdEps (N : ℝ) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom,
    ∃ X : PT D.host.E, IsTorusAt ((T.U j σ).X k) x X ∧ (∃ w, EpsBy X w) ∧ ∃ s ∈ X.Sec 1 1, s ≠ 0 ∧
      ProdBound X s 5 N i (normAt T j σ (wEt D j i) η.1 k x)

theorem eta_product_of_torus_bound {Nc nt : ℕ} {N : ℝ} (hN : (Nc : ℝ) ≤ N) (hn : nt ≤ nTerms D)
    (H : Formalism.L2.Pj.EtProd h 5 Nc nt j i η) : EtaleProductPrimes.EtProd h N j i η := fun σ hσ k x hx => by
  obtain ⟨A, hA⟩ := H σ hσ k x hx
  exact ⟨A.T, isTorusAt A, A.s, A.s_mem, A.s_ne, FixBound.prodBound hN (by rw [torusAt_r A]; exact hn) hA⟩

end Record

end GlobalTheory.EtaProdCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_baseChange_algebraMap : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z := by
  first | exact @GlobalTheory.Frames.FramedBaseChange.exists_frMap | exact GlobalTheory.Frames.FramedBaseChange.exists_frMap | (intros; apply GlobalTheory.Frames.FramedBaseChange.exists_frMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
section
noncomputable section

namespace GlobalTheory.Member.PrincLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem smul_mem_hat (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F L) : a • z ∈ GlobalTheory.AdLat.hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x, hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def congSub {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (H : AddSubgroup (Fin n → R)) (N : ℕ) :
    AddSubgroup (Fin n → R) where
  carrier := {z | ∃ y ∈ H, M *ᵥ z - z = N • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← ha, ← hb]; abel
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← ha]; abel

theorem cong_of_gen (L : Set (Fin n → E)) (S : Set (Fin n → E)) (hS : L ⊆ AddSubgroup.closure S)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h : ∀ x ∈ S, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x = N • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ z - z = N • y := by
  have h1 : ∀ x ∈ AddSubgroup.closure S, GlobalTheory.AdLat.fv F x ∈ congSub M (GlobalTheory.AdLat.hat F L) N := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact h z hz
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by funext i; simp [GlobalTheory.AdLat.fv]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_add]
      rw [this]; exact add_mem hx hy
    | neg x _ hx =>
      have : GlobalTheory.AdLat.fv F (-x) = -GlobalTheory.AdLat.fv F x := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_neg]
      rw [this]; exact neg_mem hx
  have h2 : GlobalTheory.AdLat.hat F L ≤ congSub M (GlobalTheory.AdLat.hat F L) N := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := h1 x (hS hx)
    have hz : (fun i => a ⊗ₜ[F] x i : Fin n → GlobalTheory.AdLat.RA F E) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp only [GlobalTheory.AdLat.fv, Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    refine ⟨a • y, smul_mem_hat L a ha hy, ?_⟩
    rw [hz, Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  exact fun z hz => h2 hz

theorem continuous_mulVec_sub {X R : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) (v : Fin n → R) :
    Continuous fun k => f k *ᵥ v - v :=
  (hf.matrix_mulVec continuous_const).sub continuous_const

end General

variable {D : D7}

theorem finCong_map {V : HSp D} {N : ℕ} {k : GA D V} (hk : FinCong V N k) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  exact add_mem (nsmul_mem hy N) hz

theorem finCong_one (V : HSp D) (N : ℕ) : FinCong V N 1 := by
  intro z _
  exact ⟨0, zero_mem _, by simp⟩

theorem finCong_mul {V : HSp D} {N : ℕ} {a b : GA D V} (ha : FinCong V N a) (hb : FinCong V N b) :
    FinCong V N (a * b) := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hb z hz
  obtain ⟨x, hx, e'⟩ := ha _ (finCong_map hb z hz)
  refine ⟨x + y, add_mem hx hy, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← e, ← e']
  abel

theorem finCong_inv {V : HSp D} {N : ℕ} {a : GA D V} (ha : FinCong V N a) : FinCong V N a⁻¹ := by
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hinv : ∀ z ∈ latHat V, (finHom V a⁻¹).1 *ᵥ z ∈ latHat V := by
    have hm := finCong_map ha
    rw [h1] at hm ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latC V) (finHom V a) (cF D) h3 h4 hm
      (GlobalTheory.Member.finHom_herm_det D V a).2.1
  intro z hz
  obtain ⟨y, hy, e⟩ := ha _ (hinv z hz)
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at e
  rw [neg_nsmul, ← e, neg_sub]

def levelGroup (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ FinCong V N k}
  one_mem' := ⟨one_mem _, finCong_one V N⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, finCong_mul ha.2 hb.2⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, finCong_inv ha.2⟩

theorem finCong_mem_nhds (V : HSp D) {N : ℕ} (hN : 0 < N) :
    {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, hc, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : GA D V | ∃ y ∈ latHat V,
      (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : GA D V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx : Continuous fun k : GA D V =>
        (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x :=
      continuous_mulVec_sub hc _
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun k hk => ?_
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hk
  unfold FinCong
  rw [Set.mem_ofPred_eq]
  rw [h1] at hk ⊢
  exact cong_of_gen _ _ hLS _ N fun x hx => hk x hx

theorem exists_levelK_and_nhds : ∀ (D : D7) (V : HSp D), ∀ N : ℕ,
    (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧
      (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) :=
  fun _ V N => ⟨⟨levelGroup V N, fun _ => Iff.rfl⟩, fun hN => finCong_mem_nhds V hN⟩

end GlobalTheory.Member.PrincLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeCharStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelicChar_of_heckeChar : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  first | exact @GlobalTheory.Member.exists_muVal | exact GlobalTheory.Member.exists_muVal | (intros; apply GlobalTheory.Member.exists_muVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

namespace GlobalTheory.ExpClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))

theorem expUniq : ExpUniq e F := by
  intro i P P' hP hP' gam h hEF hM hA hrel z
  have hm : ∀ z, Matrix.mulVec (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) z = h z :=
    fun z => LinearMap.toMatrix'_mulVec _ z
  have key := @GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E _ _ _ H Dw l Xo _ g _ F i P P' gam
    (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) hP hP' hEF hM hA (fun a => by rw [hm]; exact hrel a)
  have := key.2.2 z
  rwa [hm] at this

theorem expLin : ExpLin e F := by
  intro i P hP m w vs cf v hvs hv
  exact (@GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E _ _ _ H Dw l Xo _ g _ F i P hP m vs w hvs cf v).2 hv

theorem expTan : ExpTan e F := by
  intro i P hP w v hv
  refine ⟨(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).1 w v hv, fun j hj => ?_⟩
  refine (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v (e j).1 hv).2 fun j' hj' => ?_
  by_cases hjj : j' = j
  · rw [hjj]
  · exact absurd (by rw [hj, Pi.single_eq_of_ne hjj]) hj'

theorem lieEig : LieEig e F := by
  intro i P hP τ v hv he
  obtain ⟨w, hw, -⟩ := (@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).2.2 v hv
  have hs := (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v τ hw).1 he
  refine ⟨fun j => w (e.symm ⟨τ, j⟩), ?_⟩
  have hsum : (∑ j, w (e.symm ⟨τ, j⟩) • eb e τ j) = w := by
    funext k
    obtain ⟨⟨τ', m⟩, rfl⟩ := e.symm.surjective k
    by_cases hτ : τ' = τ
    · subst hτ
      exact sum_eb_apply e τ' (fun j => w (e.symm ⟨τ', j⟩)) m
    · have h0 : w (e.symm ⟨τ', m⟩) = 0 := by
        by_contra hne
        have := hs _ hne
        rw [Equiv.apply_symm_apply] at this
        exact hτ this
      rw [h0]
      simp [Finset.sum_apply, eb_apply, Sigma.mk.inj_iff, hτ]
  rw [hsum]
  exact hw

end GlobalTheory.ExpClauses

theorem GlobalTheory.exp_four_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), ExpUniq e F ∧ ExpLin e F ∧ ExpTan e F ∧ LieEig e F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ e F =>
    ⟨GlobalTheory.ExpClauses.expUniq e F, GlobalTheory.ExpClauses.expLin e F, GlobalTheory.ExpClauses.expTan e F, GlobalTheory.ExpClauses.lieEig e F⟩
end

