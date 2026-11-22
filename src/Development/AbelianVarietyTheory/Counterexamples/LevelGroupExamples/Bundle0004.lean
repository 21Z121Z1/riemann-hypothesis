import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.DetNormOneGen
section
noncomputable section

namespace GlobalTheory.LevelSubgroup

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latCo (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem latHat_eq (V : HSp D) :
    latHat V = GlobalTheory.AdLat.hat D.host.F (latCo V : Set (Fin V.rank → D.host.E)) := by
  unfold latHat GlobalTheory.AdLat.hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

theorem latCo_fg (V : HSp D) : (latCo V).FG := V.standardTuple_isLattice.fg.map _

theorem latCo_span (V : HSp D) :
    Submodule.span D.host.E (latCo V : Set (Fin V.rank → D.host.E)) = ⊤ := by
  have h := V.standardTuple_isLattice.span_eq_top
  have : (latCo V : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
  rw [this, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h0 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    have : V.hT.flip (V.frame.equivFun.symm v) = 0 := by
      refine V.frame.ext fun i => ?_
      have := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
      simp only [LinearMap.flip_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
        LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      exact mul_comm (v j) _
    exact congrArg (fun f => f x) this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

def conjEquiv (D : D7) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

theorem det_norm_one_gen {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B → B) (φ : A →+* B)
    (hφ : ∀ x, τ (φ x) = φ (σ x)) (J g : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (h : Formalism.UG.cT σ g * J * g = J) : (g.map φ).det * τ (g.map φ).det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (RingHom.map_det _ _).symm
  have h5 : (g.map φ).det = φ g.det := (RingHom.map_det _ _).symm
  rw [h2] at h1
  have h4 : g.det * σ g.det = 1 := by
    apply hJ.mul_left_cancel
    linear_combination h1
  rw [h5, hφ, ← map_mul, h4, map_one]

theorem sg_fin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : AF F ⊗[F] E) :
    GlobalTheory.AdLat.sg (Af F) c ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x) =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (sigR (AF F) (c : E →ₐ[F] E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem isUnit_det_JR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) : IsUnit (JR (F := F) (AF F) J).det := by
  have h3 : (JR (F := F) (AF F) J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
  rw [h3]
  exact (Ne.isUnit h).map _

theorem det_norm_one (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (conjEquiv D) (finHom V k).1.det = 1 :=
  det_norm_one_gen (sigR (AF D.host.F) D.sp.cm.sig) (GlobalTheory.AdLat.sg (Af D.host.F) (conjEquiv D)) _
    (sg_fin (conjEquiv D)) (JR (AF D.host.F) V.gram) (matHom V k).1 (isUnit_det_JR _ (gram_det_ne_zero V)) k.2

theorem mulVec_mem {V : HSp D} {N : ℕ} {k : GA D V} (hk : k ∈ levSet V N) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, h⟩ := hk.2 z hz
  rw [eq_add_of_sub_eq h]
  exact add_mem (nsmul_mem hy N) hz

theorem inv_mulVec_mem {V : HSp D} {k : GA D V} (hk : ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1 *ᵥ z ∈ latHat V := by
  rw [map_inv]
  rw [latHat_eq] at hk ⊢
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latCo V) (finHom V k) (conjEquiv D)
    (latCo_fg V) (latCo_span V) hk (det_norm_one V k)

def levSub (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := levSet V N
  one_mem' := ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨mul_mem ha.1 hb.1, fun z hz => ?_⟩
    obtain ⟨y, hy, h⟩ := hb.2 z hz
    obtain ⟨y', hy', h'⟩ := ha.2 _ (mulVec_mem hb z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← h, ← h']
    abel
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, fun z hz => ?_⟩
    obtain ⟨y, hy, h⟩ := ha.2 _ (inv_mulVec_mem (mulVec_mem ha) z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h
    rw [neg_nsmul, ← h]
    abel

def finSign (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : AF F ⊗[F] E :=
  pairA F 1 (-1) ⊗ₜ 1

theorem finSign_sq (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    finSign F E * finSign F E = 1 := by
  rw [finSign, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def, mul_one]
  congr 1
  exact Prod.ext (mul_one (1 : Ainf F)) (neg_mul_neg (1 : Af F) 1 |>.trans (mul_one _))

def finSignGL (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n : ℕ) : GL (Fin n) (AF F ⊗[F] E) :=
  ⟨finSign F E • 1, finSign F E • 1, by rw [smul_mul_smul_comm, finSign_sq, mul_one, one_smul],
    by rw [smul_mul_smul_comm, finSign_sq, mul_one, one_smul]⟩

theorem finSignGL_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E)
    (J : Matrix (Fin n) (Fin n) E) : finSignGL F E n ∈ HR (AF F) σ J := by
  have h : sigR (AF F) σ (finSign F E) = finSign F E := by
    change pairA F 1 (-1) ⊗ₜ σ 1 = _
    rw [map_one]; rfl
  have h2 : Formalism.UG.cT (sigR (AF F) σ) (finSign F E • (1 : Matrix (Fin n) (Fin n) _)) = finSign F E • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT, h]
    · simp [Formalism.UG.cT, hij, Ne.symm hij]
  change Formalism.UG.cT (sigR (AF F) σ) (finSign F E • 1) * JR (AF F) J * (finSign F E • 1) = JR (AF F) J
  rw [h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, finSign_sq, one_smul]

def negFin (V : HSp D) : GA D V := ⟨finSignGL _ _ _, finSignGL_mem _ _⟩

end GlobalTheory.LevelSubgroup
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
section
noncomputable section

open scoped TensorProduct Topology
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DictLocTest

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def LocClause (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
    ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩

theorem mem_dom_iff (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y : Frame X.Ψ r) :
    lact γ y ∈ X.dom ↔ y ∈ X.dom := by
  have hg : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine (map_ne_zero τ.1).2 ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hd : ∀ τ : X.Ψ, (mat (lact γ y) τ).det =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det * (mat y τ).det := by
    intro τ
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ).det = _
    exact Matrix.det_mul _ _
  simp only [Data.dom, GG, Set.mem_setOf_eq, hd, mul_ne_zero_iff, GlobalTheory.NormFactor.dmin_lact X hγ y]
  constructor
  · intro h τ
    exact ⟨(h τ).1.2, (h τ).2⟩
  · intro h τ
    exact ⟨⟨hg τ, (h τ).1⟩, (h τ).2⟩

theorem lact_rmul_lact {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ' (rmul (lact γ y) b) = lact (γ' * γ) (rmul y b) := by
  funext τ
  show (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ * mat b τ) =
    ((γ' * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * (mat y τ * mat b τ)
  simp only [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_one {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = y τ
  rw [Units.val_one, ← RingHom.mapMatrix_apply, map_one, Matrix.one_mul]
  rfl

theorem locClause_of_unif {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hK : Kf ≤ GfC V)
    (hN : ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀)
    (hth : ∀ c τ, Continuous (archM V (th c τ))) : LocClause V dict := by
  unfold DictIsUnif at hd
  obtain ⟨-, hKd, ⟨x0, -, hx0⟩, hdom, -⟩ := hd
  unfold archMat at hx0
  intro g₀
  rcases hg : dict g₀ with ⟨c, y0⟩
  refine ⟨_, hN g₀, c, fun g => rmul y0 fun τ => (mat (x0 c) τ)⁻¹ *
    Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) (g₀⁻¹ * g)) * mat (x0 c) τ, ?_, ?_⟩
  · refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    have hmul : ∀ θ (a b : GA D V), archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro θ a b
      unfold archM
      rw [map_mul, Units.val_mul, Matrix.map_mul]
    have hA : Continuous fun g : GA D V => archM V (th c τ) (g₀⁻¹ * g) := by
      simp only [hmul]
      exact continuous_const.matrix_mul (hth c τ)
    show Continuous fun g : GA D V => (mat y0 τ * ((mat (x0 c) τ)⁻¹ *
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) (g₀⁻¹ * g)) * mat (x0 c) τ) :
        Matrix (Fin r) (Fin r) ℂ)
    exact continuous_const.matrix_mul
      ((continuous_const.matrix_mul (hA.matrix_reindex _ _)).matrix_mul continuous_const)
  · rintro g ⟨k, hk, h, hh, rfl⟩
    have har : ∀ θ, archM V θ (g₀⁻¹ * (g₀ * k * h)) = archM V θ h := by
      intro θ
      have hk1 : infHom V k = 1 := MonoidHom.mem_ker.1 (hK hk)
      rw [show g₀⁻¹ * (g₀ * k * h) = k * h by group]
      unfold archM
      rw [map_mul, hk1, one_mul]
    simp only [har]
    obtain ⟨γ1, hγ1, e1⟩ := hKd k hk g₀
    rw [hg] at e1 hγ1
    dsimp only at e1 hγ1
    obtain ⟨γ2, hγ2, e2⟩ := hx0 (g₀ * k) h hh
    rw [e1] at e2 hγ2
    dsimp only at e2 hγ2
    have he : dict (g₀ * k * h) = ⟨c, lact (γ2 * γ1) (rmul y0 fun τ => (mat (x0 c) τ)⁻¹ *
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) h) * mat (x0 c) τ)⟩ := by
      rw [e2]
      exact congrArg (Sigma.mk c) (lact_rmul_lact γ2 γ1 y0 _)
    refine ⟨?_, γ2 * γ1, mul_mem hγ2 hγ1, he⟩
    have hm := hdom (g₀ * k * h)
    rw [he] at hm
    exact (mem_dom_iff (X c) (mul_mem hγ2 hγ1) _).1 hm

theorem continuous_place {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    {τ : L →+* ℂ} {θ : Ainf F ⊗[F] L →+* ℂ} (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) :
    Continuous fun z : AF F ⊗[F] L => θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] L) := ⟨rfl⟩
  haveI : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  let b := Module.finBasis F L
  let B := Algebra.TensorProduct.basis (AF F) b
  have hz : ∀ z : AF F ⊗[F] L, θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z) =
      ∑ i, θ (fstA F (B.repr z i) ⊗ₜ[F] (1 : L)) * τ (b i) := by
    intro z
    conv_lhs => rw [← B.sum_repr z]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← hθ.1, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [show (fun z : AF F ⊗[F] L => θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z)) =
    fun z => ∑ i, θ (fstA F (B.repr z i) ⊗ₜ[F] (1 : L)) * τ (b i) from funext hz]
  refine continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const
  have hf : Continuous (fstA F) := continuous_fst
  exact hθ.2.comp (hf.comp (IsModuleTopology.continuous_of_linearMap (B.coord i)))

theorem continuous_archM (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : Continuous (archM V θ) := by
  unfold archM
  have h1 : Continuous fun h : GA D V => ((matHom V h : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h1.matrix_map (continuous_place hθ)

theorem locClause_of_unif_places {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hK : Kf ≤ GfC V)
    (hN : ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀)
    (hth : ∀ c τ, ∃ τ', Formalism.MainNotions.StandardLattice.IsInfEmb τ' (th c τ)) : LocClause V dict :=
  locClause_of_unif hd hK hN fun c τ => (hth c τ).elim fun _ h => continuous_archM V h

end GlobalTheory.DictLocTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
section
noncomputable section

namespace GlobalTheory.LettersCheck

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem isInfEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (h' : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.2 ((map_ne_zero _).2 ?_)
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := sq_emb D D.host.φ₀
    rw [h, map_zero] at h1
    have h2 : (D.host.d : ℂ) = 0 := by linear_combination h1
    have h3 := D.host.qd_big.2
    have h4 : D.host.d = 0 := by exact_mod_cast h2
    omega
  show -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) ≠ 0
  exact div_ne_zero (by simp) (mul_ne_zero (normK_ne_zero D) hs)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lminor_sgn (p0 : ℕ) (i : Fin (r + 1)) :
    lminor (Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) i = ((psgn p0 i : ℝ) : ℂ) := by
  unfold lminor psgn
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range (fun a => ((sgn p0 a : ℝ) : ℂ))]
  rfl

theorem psgn_sq (p0 i : ℕ) : psgn p0 i * psgn p0 i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = P.transpose * (G.map τ * P.map (starRingEnd ℂ)) := by
  ext a b
  simp [gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem unit_of_x0Orth (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : IsOrthogonalFrame X x₀) :
    (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) ∈ X.dom ∧
      ∀ τ i, ‖dmin X.Gm (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) τ i‖ = 1 := by
  have hd : ∀ (τ : X.Ψ) i, dmin X.Gm (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) τ i =
      ((psgn X.p0 i : ℝ) : ℂ) := fun τ i => by
    rw [← lminor_sgn, ← h τ.1 τ.2]
    rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩
  · show (x₀ τ.1).det ≠ 0
    intro h0
    have h1 := congrArg Matrix.det (h τ.1 τ.2)
    rw [gram_eq, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h1
    refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
    unfold sgn
    split_ifs <;> simp
  · rw [hd, Complex.ofReal_re, psgn_sq]
    exact one_pos
  · rw [hd, Complex.norm_real]
    have h := congrArg abs (psgn_sq X.p0 i)
    rw [abs_mul, abs_one] at h
    have h0 := abs_nonneg (psgn X.p0 i)
    rw [Real.norm_eq_abs]
    nlinarith

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem relab_val (c : Coeff l) (τ : E →+* ℂ) : relab c c.F.val.toRingHom τ = τ := by
  ext a
  rfl

end GlobalTheory.LettersCheck
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.PiTwistNegation
section
noncomputable section
namespace GlobalTheory.Survey.PiTwistNegation
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

def withPi (X : ErrX D) (p : Fin 2 → 𝓞 D.host.E) (hK : ∀ i, ((p i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K)
    (hn : ∀ i, p i * barE D (p i) = (D.host.g i : 𝓞 D.host.E)) : ErrX D :=
  { X with
    piG := p
    piG_K := hK
    piG_norm := fun i => by
      rw [← barE_eq_conj]
      have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) (hn i)
      rw [map_mul, map_natCast] at this
      exact this }

def swapX (X : ErrX D) : ErrX D :=
  withPi X (fun i => barE D (X.piG i)) (barE_piG_mem X) fun i => by
    rw [barE_barE, mul_comm]; exact piG_mul_barE X i

def negX (X : ErrX D) : ErrX D :=
  withPi X (fun i => -X.piG i) (fun i => by
    have := neg_mem (X.piG_K i)
    simpa using this) fun i => by
    rw [map_neg, neg_mul_neg]; exact piG_mul_barE X i

theorem halfI_ne_top (T : Core D) (i : Fin 2) : halfI T i ≠ ⊤ := by
  intro h
  have hc : ((T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).comap
      (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊤ := by
    rw [show (T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊤ from h, Ideal.comap_top]
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hc
  exact (T.pb i).isPrime.ne_top hc

theorem bar_piOf_mem_K (T : Core D) (X : ErrX D) (i : Fin 2) :
    ((barE D (piOf T X i) : 𝓞 D.host.E) : D.host.E) ∈ D.host.K := by
  classical
  unfold piOf
  split_ifs
  · rw [barE_barE]; exact X.piG_K i
  · exact barE_piG_mem X i

def orientX (T : Core D) (X : ErrX D) : ErrX D :=
  withPi X (fun i => barE D (piOf T X i)) (bar_piOf_mem_K T X) fun i => by
    rw [barE_barE, mul_comm]; exact piOf_mul_barE T X i

theorem halfEX_iff_le (T : Core D) (h : LawsM T) (X : ErrX D) :
    HalfEX T X ↔ ∀ i, T.Q.l.Mb ≤ Ideal.span {barE D (X.piG i)} := by
  have hle : ∀ i, T.Q.l.Mb ≤ halfI T i := by
    intro i
    rw [Mb_eq T h]
    fin_cases i
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_right
  refine forall_congr' fun i => ⟨fun hb => ?_, fun hM => ?_⟩
  · rw [← (piOf_eq_bar_iff T h X i).2 hb, span_piOf T h]; exact hle i
  · by_contra hb
    have hp : piOf T X i = X.piG i := by
      classical
      unfold piOf; rw [if_neg hb]

    have h1 : T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {barE D (X.piG i)} := by
      rw [← hp, ← bar_core T, span_bar_piOf T h]; exact Ideal.map_mono (hle i)
    have ht : Ideal.span {barE D (X.piG i)} = ⊤ := by
      rw [eq_top_iff, ← T.Q.l.coprime]; exact sup_le hM h1
    have hu : IsUnit (X.piG i) := by
      have := (Ideal.span_singleton_eq_top.1 ht).map (barE D)
      rwa [barE_barE] at this
    apply halfI_ne_top T i
    rw [← span_piOf T h X i, hp, Ideal.span_singleton_eq_top]; exact hu

end GlobalTheory.Survey.PiTwistNegation
end
end

