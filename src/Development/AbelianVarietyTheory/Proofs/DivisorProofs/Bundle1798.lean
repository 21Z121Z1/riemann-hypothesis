import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMatMapSelf
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.CompIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_cA {R : Type} [CommRing R] [Algebra F R] (f : AF F →ₐ[F] R) (σ : E →ₐ[F] E) (y : AE F E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (cA σ y) =
      Algebra.TensorProduct.map (AlgHom.id R R) σ (Algebra.TensorProduct.map f (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_unit {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (ρ : A →+* B) (c : A → A) (c' : B → B)
    (hc : ∀ y, ρ (c y) = c' (ρ y)) (M J : Matrix (Fin m) (Fin m) A) :
    (Mᵀ * J * M.map c).map ρ = (M.map ρ)ᵀ * J.map ρ * (M.map ρ).map c' := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map]
  congr 2
  funext y
  exact hc y

theorem mapNU_mul {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (S : A →ₙ+* B) (X Y : Matrix (Fin m) (Fin m) A) :
    (X * Y).map S = X.map S * Y.map S := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

def liftMat (v : Pl F) (m : ℕ) : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E) →* Matrix (Fin m) (Fin m) (AE F E) where
  toFun h := 1 + (h - 1).map (Supp.singleTens E v)
  map_one' := by simp
  map_mul' a b := by
    have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [e, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), mapNU_mul]
    noncomm_ring

theorem liftMat_apply (v : Pl F) {m : ℕ} (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    liftMat v m h = 1 + (h - 1).map (Supp.singleTens E v) := rfl

theorem liftMat_map_zero {B : Type} [CommRing B] (v : Pl F) {m : ℕ} (ρ : AE F E →+* B)
    (hρ : ∀ y, ρ (Supp.singleTens E v y) = 0) (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    (liftMat v m h).map ρ = 1 := by
  rw [liftMat_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map]
  have : (ρ ∘ Supp.singleTens E v) = fun _ => 0 := funext hρ
  rw [this]
  ext i j
  simp

theorem liftMat_map_self (v : Pl F) {m : ℕ} (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    (liftMat v m h).map (compFin F E v) = h := by
  rw [liftMat_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map]
  have : (compFin F E v ∘ Supp.singleTens E v) = id := funext (Supp.compFin_singleTens_self v)
  rw [this, Matrix.map_id]
  abel

theorem incM_map (v : Pl F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (incM F J).map (compFin F E v) = Jv v J := by
  ext i j
  exact Supp.compFin_one_tmul v (J i j)

variable (σ : E →ₐ[F] E) {m : ℕ} (Y : Spc F E m) (v : Pl F)

variable (m) in

def fwdGL : GL (Fin m) (AE F E) →* GL (Fin m) (Fv F v ⊗[F] E) :=
  Units.map (compFin F E v).mapMatrix.toMonoidHom

theorem fwd_mem (g : UA σ Y.J) : fwdGL m v g.1 ∈ UG (cv σ v) (Jv v Y.J) := by
  have hg : (g.1 : Matrix (Fin m) (Fin m) (AE F E))ᵀ * incM F Y.J * (g.1 : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ) =
      incM F Y.J := g.2
  show ((g.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v))ᵀ * Jv v Y.J *
      ((g.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v)).map (cv σ v) = Jv v Y.J
  rw [← incM_map v Y.J, ← map_unit (compFin F E v) (cA σ) (cv σ v) (fun y => map_cA (evFin F v) σ y), hg]

def fwd : UAtGrp σ Y (evFin F v) →* UG (cv σ v) (Jv v Y.J) :=
  ((fwdGL m v).comp ((UG (cA σ) (incM F Y.J)).subtype.comp (UAtGrp σ Y (evFin F v)).subtype)).codRestrict _
    (fun g => fwd_mem σ Y v g.1)

variable (m) in

def bwdGL : GL (Fin m) (Fv F v ⊗[F] E) →* GL (Fin m) (AE F E) := Units.map (liftMat v m)

theorem bwd_mem (h : UG (cv σ v) (Jv v Y.J)) : bwdGL m v h.1 ∈ UG (cA σ) (incM F Y.J) := by
  have hh : (h.1 : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E))ᵀ * Jv v Y.J *
      (h.1 : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)).map (cv σ v) = Jv v Y.J := h.2
  show (liftMat v m h.1.1)ᵀ * incM F Y.J * (liftMat v m h.1.1).map (cA σ) = incM F Y.J
  ext i j
  apply Supp.adTens_ext
  · intro w
    have e := congrArg (fun M => M i j) (map_unit (compInf F E w) (cA σ)
      (Algebra.TensorProduct.map (AlgHom.id w.Completion w.Completion) σ) (fun y => map_cA (evInf F w) σ y)
      (liftMat v m h.1.1) (incM F Y.J))
    rw [Matrix.map_apply] at e
    rw [e, liftMat_map_zero v _ (fun y => Supp.compInf_singleTens w v y), Matrix.transpose_one, Matrix.one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    rfl
  · intro u
    have e := congrArg (fun M => M i j) (map_unit (compFin F E u) (cA σ) (cv σ u) (fun y => map_cA (evFin F u) σ y)
      (liftMat v m h.1.1) (incM F Y.J))
    rw [Matrix.map_apply] at e
    rw [e]
    rcases eq_or_ne u v with rfl | hu
    · rw [liftMat_map_self, incM_map, hh]
      exact (congrArg (fun M => M i j) (incM_map u Y.J)).symm
    · rw [liftMat_map_zero v _ (fun y => Supp.compFin_singleTens_ne hu y), Matrix.transpose_one, Matrix.one_mul,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      rfl

theorem liftMat_at (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) : At (evFin F v) (liftMat v m h - 1) := by
  intro u hu
  rw [liftMat_apply, add_sub_cancel_left]
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, mul_comm, Supp.singleTens_mul]
  have e : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    show evFin F v u ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [e, mul_zero, map_zero]
  rfl

def bwdU : UG (cv σ v) (Jv v Y.J) →* UA σ Y.J :=
  ((bwdGL m v).comp (UG (cv σ v) (Jv v Y.J)).subtype).codRestrict _ (fun h => bwd_mem σ Y v h)

def bwd : UG (cv σ v) (Jv v Y.J) →* UAtGrp σ Y (evFin F v) :=
  (bwdU σ Y v).codRestrict _ (fun h => liftMat_at v h.1.1)

theorem lift_comp (z : AE F E) (hz : At (evFin F v) z) : Supp.singleTens E v (compFin F E v z) = z := by
  have h1 := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero, Algebra.smul_def] at h1
  conv_rhs => rw [h1]
  rw [show algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) = Supp.singleTens E v 1 from rfl, Supp.singleTens_mul,
    one_mul]

theorem bwd_fwd (g : UAtGrp σ Y (evFin F v)) : bwd σ Y v (fwd σ Y v g) = g := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  show liftMat v m ((g.1.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v)) = g.1.1
  have hg : At (evFin F v) (mat g.1 - 1) := g.2
  have e : (g.1.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v) - 1 =
      ((g.1.1 : Matrix (Fin m) (Fin m) (AE F E)) - 1).map (compFin F E v) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [liftMat_apply, e, Matrix.map_map]
  ext i j
  have hz : At (evFin F v) (((g.1.1 : Matrix (Fin m) (Fin m) (AE F E)) - 1) i j) := fun u hu => by
    have := congrArg (fun M => M i j) (hg u hu)
    simp only [Matrix.smul_apply, Matrix.zero_apply] at this
    exact this
  rw [Matrix.add_apply, Matrix.map_apply, Function.comp_apply, lift_comp v _ hz, Matrix.sub_apply]
  abel

theorem fwd_bwd (h : UG (cv σ v) (Jv v Y.J)) : fwd σ Y v (bwd σ Y v h) = h := by
  apply Subtype.ext; apply Units.ext
  exact liftMat_map_self v _

end GlobalTheory.HoweLocal.CompIso

namespace GlobalTheory.HoweLocal

open CompIso in

theorem compIso_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (m : ℕ) (Y : Spc F E m) (v : Pl F), ∃ e : UAtGrp σ Y (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v Y.J),
      GlobalTheory.HoweLocal.IsCompIso σ Y v e := by
  intro F E _ _ _ _ _ σ _ m Y v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have hcf : Continuous (compFin F E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
      ((RestrictedProduct.continuous_eval v).comp continuous_snd)
  have hst : Continuous (Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  refine ⟨MonoidHom.toMulEquiv (fwd σ Y v) (bwd σ Y v) (MonoidHom.ext (bwd_fwd σ Y v)) (MonoidHom.ext (fwd_bwd σ Y v)),
    fun g => rfl, ?_, ?_⟩
  · show Continuous (fwd σ Y v)
    refine Continuous.subtype_mk ?_ _
    exact (Continuous.units_map _ (continuous_id.matrix_map hcf)).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · show Continuous (bwd σ Y v)
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (Continuous.units_map _ (continuous_const.add ((continuous_id.sub continuous_const).matrix_map hst))).comp
      continuous_subtype_val

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePairExtensionCosSqBound
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

open GlobalTheory.Twist (resM)

theorem leviForm_congr_germ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u u' : E → ℝ} {z : E} (h : u =ᶠ[𝓝 z] u') :
    leviForm u z = leviForm u' z := by
  unfold leviForm ddbar
  refine del_congr ?_
  filter_upwards [h.eventuallyEq_nhds] with x hx
  exact dbar_congr (hx.mono fun w hw => by simp only [hw])

theorem green_algebra (π A B v bc bc' ch ch' lA lB x y N : ℝ) (n : ℕ) (hπ : π ≠ 0) (hA : 0 < A)
    (hB : 0 < B) (hN : N = v * A * B) (hx : x = (A * B - N) * (π * bc))
    (hy : y = (B * A - N) * (π * bc')) (hc : ch = -lA / π) (hc' : ch' = -lB / π) :
    v ^ (n + 1) * (ch - ch') + (n + 1) * v ^ n * (1 - v) * (bc - bc') =
      -(1 / π) * ((n + 1) * (N / (A * B)) ^ n * ((y - x) / (A * B)) +
        (N / (A * B)) ^ (n + 1) * (lA - lB)) := by
  have e : N / (A * B) = v := by rw [hN]; field_simp
  rw [e, hx, hy, hN, hc, hc']
  field_simp
  ring

theorem form_frame_re_pos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : X.Modules} (g : Met p σ L 1) {U : X.Opens} {t : Γ(L, U)}
    (ht : IsFrame (fun _ : Fin 1 => t)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (g.form t t y).re := by
  let c₀ : VB.Chart L 1 := ⟨U, fun _ => t, ht⟩
  have h₀ := g.form_frame c₀ hy 0 0
  have h₁ := (g.posDef c₀ y hy).diag_pos (i := 0)
  have h₂ : g.form t t y = g.G c₀ y 0 0 := h₀
  rw [h₂]
  exact (Complex.pos_iff.1 h₁).1

theorem green_density {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {V L Q L' Q' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V} {m' : V ⟶ Q'}
    {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
    (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1)
    (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (h : Met p σ V (1 + 1)) (H : h.IsCInf) {v : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (n : ℕ)
    {m₀ : AlgChart p σ 1 → CxPts p σ → ℂ}
    (hm₁ : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => m₀ c (c.e.symm v)) (c.e y))
    (hm₃ : ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) →
      IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U →
      m₀ c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
        (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
        (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y))
    (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y -
        c.chernDens (h.restrict hl' hL').detWeight y) +
      (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y -
        Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y) =
    (dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y)
      (EuclideanSpace.single 0 1)).re := by
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hL (y.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := hL' (y.1 (IsLocalRing.closedPoint ℂ))
  have hU : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hx₁, mem_ptsIn.2 hx₂⟩
  obtain ⟨U, hUdef⟩ : ∃ U, U = U₁ ⊓ U₂ := ⟨_, rfl⟩
  rw [← hUdef] at hU
  obtain ⟨t, ht⟩ : ∃ t : Γ(L, U), IsFrame (fun _ : Fin 1 => t) := by
    subst hUdef
    refine ⟨resM L inf_le_left (e₁ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (e₁ 0)) =
        fun i => resM L inf_le_left (e₁ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₁.res inf_le_left
  obtain ⟨t', ht'⟩ : ∃ t' : Γ(L', U), IsFrame (fun _ : Fin 1 => t') := by
    subst hUdef
    refine ⟨resM L' inf_le_right (e₂ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L' (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (e₂ 0)) =
        fun i => resM L' inf_le_right (e₂ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₂.res inf_le_right
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy hU
  have hn := ho.mem_nhds hm

  have hG : MContDiffAt ∞ (fun x => h.gram ![l.app U t, l'.app U t'] (c.e.symm x)) (c.e y) :=
    (H.gram ![l.app U t, l'.app U t'] hU).mContDiffAt c hy
  have dq : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y) :=
    (hG 1 0).of_le (by norm_cast)
  have da₀ : ContDiffAt ℝ 2 (fun x => h.form (l.app U t) (l.app U t) (c.e.symm x)) (c.e y) :=
    (hG 0 0).of_le (by norm_cast)
  have da₁ : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l'.app U t') (c.e.symm x)) (c.e y) :=
    (hG 1 1).of_le (by norm_cast)
  have da : ContDiffAt ℝ 2 (fun x => (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ da₀
  have da' : ContDiffAt ℝ 2 (fun x => (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ da₁

  have pa : 0 < (h.form (l.app U t) (l.app U t) y).re := by
    have := form_frame_re_pos (h.restrict hl hL) ht hU
    rwa [h.form_restrict hl hL _ _ hU] at this
  have pa' : 0 < (h.form (l'.app U t') (l'.app U t') y).re := by
    have := form_frame_re_pos (h.restrict hl' hL') ht' hU
    rwa [h.form_restrict hl' hL' _ _ hU] at this

  have hdb : dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y)
      (EuclideanSpace.single 0 1) = (((-(1 / Real.pi) : ℝ)) : ℂ) *
        dbar (angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
          (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
          (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1))
          (c.e y) (EuclideanSpace.single 0 1) := by
    have e₁ := dbar_const_smul (((-(1 / Real.pi) : ℝ)) : ℂ)
      ((hm₁ c y hy).differentiableAt (by norm_num))
    have e₂ := dbar_congr (z := c.e y) (f := fun v => m₀ c (c.e.symm v))
      (g := angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
          (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
          (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1))
      (by
        filter_upwards [hn] with x hx
        have := hm₃ U t t' ht ht' c (c.e.symm x) (c.e.map_target hx.1) hx.2
        rwa [c.e.right_inv hx.1] at this)
    simp only [smul_eq_mul] at e₁
    rw [e₁, e₂]
    rfl
  have hcalc := GlobalTheory.T.dbar_angleForm_re_eq _ n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
    (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
    (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y)
    da da' dq (by simpa only [e₀] using pa) (by simpa only [e₀] using pa')

  have hX := GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l m w) h hS hL hQ H U t (l'.app U t') ht c y hy hU
  have hY := GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l' m' w') h hS' hL' hQ' H U t' (l.app U t) ht' c y hy hU
  have hY' : ‖del (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y)
        (EuclideanSpace.single 0 1) - h.form (l'.app U t') (l.app U t) y *
        del (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y)
        (EuclideanSpace.single 0 1)‖ ^ 2 =
      ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
        ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS' hL' hQ' c y) := by
    have e₁ : (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) =
        fun x => (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) (c.e.symm x)) := by
      funext x; rw [h.conj_form]
    have e₂ : h.form (l.app U t) (l'.app U t') y =
        (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) y) := by rw [h.conj_form]
    have hY2 : ‖dbar (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) (c.e y)
          (EuclideanSpace.single 0 1) - h.form (l.app U t) (l'.app U t') y *
          dbar (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y)
          (EuclideanSpace.single 0 1)‖ ^ 2 =
        ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
          ‖h.form (l.app U t) (l'.app U t') y‖ ^ 2) * (Real.pi * h.bcDens hS' hL' hQ' c y) := hY
    rw [e₁, e₂, dbar_conj, dbar_ofReal, ← map_mul, ← map_sub, Complex.norm_conj,
      Complex.norm_conj] at hY2
    exact hY2
  have c₁ := (chernDens_curve k X p σ).2 L (h.restrict hl hL) (H.restrict hl hL) U t ht c y hy hU
  have c₂ := (chernDens_curve k X p σ).2 L' (h.restrict hl' hL') (H.restrict hl' hL') U t' ht' c y hy hU
  have l₁ : leviForm (fun x => Real.log ((h.restrict hl hL).form t t (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl hL _ _ hx.2])
  have l₂ : leviForm (fun x => Real.log ((h.restrict hl' hL').form t' t' (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl' hL' _ _ hx.2])
  rw [l₁] at c₁
  rw [l₂] at c₂
  simp only [e₀] at hcalc
  rw [hdb, Complex.re_ofReal_mul, hcalc]
  exact green_algebra Real.pi _ _ (v y) _ _ _ _ _ _ _ _ _ n Real.pi_ne_zero pa pa'
    (hv U t t' y hU) hX hY' c₁ c₂

theorem green_cosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ V (1 + 1)), h.IsCInf → ∀ v : CxPts p σ → ℝ, IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ 1) y => v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y - c.chernDens (h.restrict hl' hL').detWeight y) + (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y - Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) = 0 := by
  intro k _ X p σ _ _ _ hAn V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H v hv n
  obtain ⟨m₀, hm₁, hm₂, hm₃⟩ := GlobalTheory.T.exists_C1_density_for_line_pair k X p σ V L L' (1 + 1) h l l' H hl hl' hL hL' n
  have st := GlobalTheory.T.chartwise_C1_density_of_compatible k X p σ hAn (fun c y => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c y)
    (fun c y hy => contDiffAt_const.mul (hm₁ c y hy))
    (fun c c' y hy hy' => by rw [hm₂ c c' y hy hy']; ring)
  rw [← st]
  exact total_congr fun c y hy =>
    green_density hS hS' hL hQ hL' hQ' hl hl' h H hv n hm₁ hm₃ c hy

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
section
noncomputable section

namespace GlobalTheory.ThK.LiftPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def rtr {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (x : UA σ J) (u : UA σ J → ℂ) : UA σ J → ℂ := fun y => u (y * x)

def trSpan {G : Type} [Group G] {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (L : G →* UA σ J) (f : UA σ J → ℂ) :
    Submodule ℂ (UA σ J → ℂ) :=
  Submodule.span ℂ (Set.range fun g => rtr (L g) f)

def liftSk (h : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) : GL (Fin m) (Fv F v) →* UA σ J :=
  GlobalTheory.SplitUnitLift.liftU h τ J (-1) (fun i j => by rw [hJ, map_neg, map_one, neg_one_mul])
    (by rw [show (J.map τ).det = τ J.det from (AlgHom.map_det τ J).symm]; exact isUnit_iff_ne_zero.2 ((map_ne_zero τ).2 hd))

def thPair {n m : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JY : Matrix (Fin m) (Fin m) E}
    (om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ)) (g : UA σ JX) (μ : Measure (UA σ JY))
    (𝓕 : Set (UA σ JY)) (u : UA σ JY → ℂ) (Φ : (Fin n × Fin m → AF F) → ℂ) : ℂ :=
  ∫ h in 𝓕, u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldLP (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

def modelA {v : Pl F} (α : (Fv F v)ˣ →* ℂˣ) (n : ℕ) {m : ℕ} (h : GL (Fin m) (Fv F v))
    (Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) : Matrix (Fin n) (Fin m) (Fv F v) → ℂ := fun X =>
  (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
    ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
    Ψ (X * ((h⁻¹ : GL (Fin m) (Fv F v)) : Matrix (Fin m) (Fin m) (Fv F v))ᵀ)

end GlobalTheory.ThK.LiftPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentConjugationSignStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_conjugation_sign : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ f : AE F E,
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  first | exact @GlobalTheory.SwapAtSplit.exists_swap_elt | exact GlobalTheory.SwapAtSplit.exists_swap_elt | (intros; apply GlobalTheory.SwapAtSplit.exists_swap_elt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubledStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weyl_element_doubled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  first | exact @GlobalTheory.DblDiag.swap_at_place | exact GlobalTheory.DblDiag.swap_at_place | (intros; apply GlobalTheory.DblDiag.swap_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationGeOfIntegralAtPrimeStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanValuation_ge_of_integral_at_prime : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | exact GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField : GlobalTheory.ColNorms.FamilyVectors := by
  first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)
end

