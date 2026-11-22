import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

section General

variable {R k : Type} [CommRing R] [CommRing k] {b a : ℕ}

open Classical in

theorem int_mul (O : Subring R) (ρ : O →+* k) (z : Matrix (Fin b) (Fin b) O) (y : Matrix (Fin a) (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, (z.map O.subtype * N * y.map O.subtype) i j ∈ O) ∧
    (Matrix.of fun i j => if h : (z.map O.subtype * N * y.map O.subtype) i j ∈ O then
        ρ ⟨(z.map O.subtype * N * y.map O.subtype) i j, h⟩ else 0) =
      z.map ρ * (Matrix.of fun i j => if h : N i j ∈ O then ρ ⟨N i j, h⟩ else 0) * y.map ρ := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix (Fin b) (Fin a) O, N = M.map O.subtype :=
    ⟨Matrix.of fun i j => ⟨N i j, h i j⟩, by ext i j; rfl⟩
  have key : z.map O.subtype * M.map O.subtype * y.map O.subtype = (z * M * y).map O.subtype := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have mem : ∀ i j, (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O := fun i j => by
    rw [key]; exact ((z * M * y) i j).2
  refine ⟨mem, ?_⟩
  have lhs : (Matrix.of fun i j => if h : (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O then
      ρ ⟨(z.map O.subtype * M.map O.subtype * y.map O.subtype) i j, h⟩ else 0) = (z * M * y).map ρ := by
    ext i j
    rw [Matrix.of_apply, dif_pos (mem i j), Matrix.map_apply]
    congr 1
    exact Subtype.ext (congrFun (congrFun key i) j)
  have mid : (Matrix.of fun i j => if h : M.map O.subtype i j ∈ O then ρ ⟨M.map O.subtype i j, h⟩ else 0) = M.map ρ := by
    ext i j
    rw [Matrix.of_apply, dif_pos (h i j)]
    rfl
  rw [lhs, mid, Matrix.map_mul, Matrix.map_mul]

theorem cancel (Z : GL (Fin b) R) (Y : GL (Fin a) R) (N : Matrix (Fin b) (Fin a) R) :
    Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val = N := by
  calc Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val
      = (Z.val * (Z⁻¹).val) * N * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem move {A : Type} [CommRing A] (f : A →+* R) (βS G Y : GL (Fin a) R) (βT H Z : GL (Fin b) R)
    (hY : βS * Y * βS⁻¹ = G) (hZ : βT * Z * βT⁻¹ = H)
    (g : Matrix (Fin a) (Fin a) A) (h : Matrix (Fin b) (Fin b) A) (hg : g.map f = G.val) (hh : h.map f = (H⁻¹).val)
    (x : Matrix (Fin b) (Fin a) A) :
    (βT⁻¹).val * (h * x * g).map f * βS.val = (Z⁻¹).val * ((βT⁻¹).val * x.map f * βS.val) * Y.val := by
  have eH : (H⁻¹).val = βT.val * ((Z⁻¹).val * (βT⁻¹).val) := by
    rw [← hZ, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  have eG : G.val = βS.val * (Y.val * (βS⁻¹).val) := by
    rw [← hY, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [Matrix.map_mul, Matrix.map_mul, hg, hh, eH, eG]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc (βT⁻¹).val βT.val, Units.inv_mul, Matrix.one_mul]

private theorem bc_mul_restrict_mul_bc_eq (O : Subring R) (ρ : O →+* k) (z : GL (Fin b) O) (y : GL (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, ((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O) ∧
    (Matrix.of fun i j => @dite _ (((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O)
        (Classical.propDecidable _) (fun h => ρ ⟨_, h⟩) (fun _ => 0)) =
      (Formalism.UG.bc ρ z).val *
        (Matrix.of fun i j => @dite _ (N i j ∈ O) (Classical.propDecidable _) (fun h => ρ ⟨N i j, h⟩) (fun _ => 0)) *
        (Formalism.UG.bc ρ y).val := by
  have ez : (Formalism.UG.bc O.subtype z).val = z.val.map O.subtype := rfl
  have ey : (Formalism.UG.bc O.subtype y).val = y.val.map O.subtype := rfl
  have ez' : (Formalism.UG.bc ρ z).val = z.val.map ρ := rfl
  have ey' : (Formalism.UG.bc ρ y).val = y.val.map ρ := rfl
  rw [ez, ey, ez', ey']
  exact GlobalTheory.FrameRed.int_mul O ρ z.val y.val N h

end General

variable {D : D7}

theorem isIntM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) :
    IsIntM (D := D) ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) ∧
    ∀ PP, redM (D := D) PP ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) =
      (Formalism.UG.bc (resS D.host.F PP) z).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  exact ⟨(bc_mul_restrict_mul_bc_eq _ (RingHom.id _) z y N h).1, fun PP => (bc_mul_restrict_mul_bc_eq _ (resS D.host.F PP) z y N h).2⟩

theorem mt_map (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (finE V g).val := rfl

theorem frMapO_actO {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {g : GA D S} {h : GA D T} {y : GL (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    {z : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : frGL βS y = finE S g) (hz : frGL βT z = finE T h) (x : WO S T) :
    frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) =
      ((intGL D.host.F D.host.E _ z)⁻¹).val * frMapO S T βS βT x * (intGL D.host.F D.host.E _ y).val := by
  have hY : βS * intGL D.host.F D.host.E _ y * βS⁻¹ = finE S g := by rw [← hy]; rfl
  have hZ : βT * intGL D.host.F D.host.E _ z * βT⁻¹ = finE T h := by rw [← hz]; rfl
  have hg : (Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) = (finE S g).val := by rw [inv_inv]; exact GlobalTheory.FrameRed.mt_map S g
  have hh : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((finE T h)⁻¹).val := by rw [GlobalTheory.FrameRed.mt_map, map_inv]
  show (βT⁻¹).val * (Formalism.L2.Theta.mt T h⁻¹ * x * Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) * βS.val = _
  exact GlobalTheory.FrameRed.move (toEAf D) βS (finE S g) (intGL D.host.F D.host.E _ y) βT (finE T h)
    (intGL D.host.F D.host.E _ z) hY hZ _ _ hg hh x

theorem isIntM_iff {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) :
    IsIntM (D := D) (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) ↔
      IsIntM (D := D) N := by
  constructor
  · intro hM
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z y⁻¹ hM).1
    rwa [map_inv (intGL D.host.F D.host.E a) y, GlobalTheory.FrameRed.cancel] at h1
  · intro hN
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y hN).1
    rwa [map_inv (intGL D.host.F D.host.E b) z] at h1

theorem redM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) (PP : Pl D.host.E) :
    redM (D := D) PP (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) =
      ((Formalism.UG.bc (resS D.host.F PP) z)⁻¹).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y h).2 PP
  rwa [map_inv (intGL D.host.F D.host.E b) z, map_inv (Formalism.UG.bc (resS D.host.F PP)) z] at h1

theorem frMapO_actO_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  intro D S T βS βT g h hg hh x
  unfold St at hg hh
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hg
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hh
  have e := GlobalTheory.FrameRed.frMapO_actO hy hz x
  refine ⟨?_, fun hI PP => ?_⟩
  · rw [e]
    exact GlobalTheory.FrameRed.isIntM_iff z y _
  · rw [e, GlobalTheory.FrameRed.redM_mul z y hI PP]
    have a : redFn βS PP (finE S g) = Formalism.UG.bc (resS D.host.F PP) y := by
      rw [← hy]; exact redFn_frGL βS PP y
    have b : redFn βT PP (finE T h) = Formalism.UG.bc (resS D.host.F PP) z := by
      rw [← hz]; exact redFn_frGL βT PP z
    rw [a, b]

end GlobalTheory.FrameRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddings
section
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory

theorem minpoly_coeff_le_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (w : InfinitePlace F) (j : ℕ) :
    w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E *
      ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  set M : ℝ≥0 := max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) with hM
  set p := minpoly F x
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h1 : p.Monic := minpoly.monic hx
  have hd : p.natDegree ≤ Module.finrank F E := minpoly.natDegree_le x
  have h3 : ∀ z ∈ (p.map w.embedding).roots, ‖z‖ ≤ (M : ℝ) := by
    intro z hz
    have hz' : z ∈ p.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨h1.ne_zero, ?_⟩
      have := (Polynomial.mem_roots (Polynomial.map_monic_ne_zero h1)).1 hz
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact this
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hz'
    obtain ⟨ψ, rfl⟩ := hz'
    let τ : EmbOver E w := ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
    have : ‖ψ x‖₊ ≤ M :=
      le_trans (Finset.le_sup (f := fun τ : EmbOver E w => ‖τ.1 x‖₊) (Finset.mem_univ τ)) (le_max_right _ _)
    exact_mod_cast this
  have key := Polynomial.coeff_le_of_roots_le (f := w.embedding) j h1 (IsAlgClosed.splits _) h3
  rw [Polynomial.coeff_map] at key
  have hw : w (p.coeff j) = ‖w.embedding (p.coeff j)‖ := (InfinitePlace.norm_embedding_eq w _).symm
  rw [hw]
  refine key.trans ?_
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left _ _
  have hpow : (M : ℝ) ^ (p.natDegree - j) ≤ (M : ℝ) ^ Module.finrank F E :=
    pow_le_pow_right₀ hM1 (le_trans (Nat.sub_le _ _) hd)
  have hch : ((p.natDegree.choose j : ℕ) : ℝ) ≤ 2 ^ Module.finrank F E := by
    have := (Nat.choose_le_two_pow p.natDegree j).trans (Nat.pow_le_pow_right (by norm_num) hd)
    exact_mod_cast this
  rw [mul_comm]
  exact mul_le_mul hch hpow (by positivity) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfForallApprox
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLocApprox

theorem integral_eq_zero_of_forall_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {v : X → ℂ} {w : X → ℝ}
    (hw : Integrable w μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ u : X → ℂ, Integrable u μ ∧ ∫ x, u x ∂μ = 0 ∧ ∀ x, ‖u x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  by_cases hv : Integrable v μ
  swap
  · exact integral_undef hv
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨u, hu, h0, hn⟩ := h ε hε
    have e : ∫ x, (u x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub hu hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

variable {D : D7} {V : HSp D}

def LocApprox (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (ψ : Fin n → GA D V → ℂ),
    (∀ l, Continuous (ψ l) ∧ (∀ γ ∈ GQ V, ∀ g, ψ l (γ * g) = ψ l g) ∧ IsCuspFun V (ψ l)) ∧
    ∀ x ∈ C, ‖f x - ∑ l, ψ l x‖ < ε

theorem leftInv_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g := by
  intro γ hγ g
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, ψ, hψ, happ⟩ := h {γ * g, g} (Set.toFinite _).isCompact (ε / 2) (by positivity)
  have e : ∑ l, ψ l (γ * g) = ∑ l, ψ l g := Finset.sum_congr rfl fun l _ => (hψ l).2.1 γ hγ g
  have h1 := happ (γ * g) (by simp)
  have h2 := happ g (by simp)
  rw [dist_eq_norm]
  have e' : f (γ * g) - f g = (f (γ * g) - ∑ l, ψ l (γ * g)) - (f g - ∑ l, ψ l g) := by rw [e]; ring
  rw [e']
  linarith [norm_sub_le (f (γ * g) - ∑ l, ψ l (γ * g)) (f g - ∑ l, ψ l g)]

theorem isCuspFun_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : IsCuspFun V f := by
  have hl := leftInv_of_locApprox h
  rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) →
      IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl'
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl' μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g :=
    continuous_subtype_val.mul continuous_const
  have hw : Integrable (fun _ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (1 : ℝ)) (μ.restrict 𝓕) := by
    simpa using (hint (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl).norm
  refine integral_eq_zero_of_forall_approx (μ := μ.restrict 𝓕) (v := fun n => f (n.1 * g)) hw fun ε hε => ?_
  obtain ⟨m, ψ, hψ, happ⟩ := h _ (hK.image hcont) ε hε
  refine ⟨fun n => ∑ l, ψ l (n.1 * g), integrable_finset_sum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1, ?_,
    fun n => ?_⟩
  · rw [integral_finset_sum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1]
    exact Finset.sum_eq_zero fun l _ =>
      (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ l).2.2 W hW μ hμ 𝓕 h𝓕 g
  · obtain ⟨γ, hγ, hk⟩ := hKs n
    have e1 : f (n.1 * g) = f ((γ * n).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl _ hγ _).symm
    have e2 : ∀ l, ψ l (n.1 * g) = ψ l ((γ * n).1 * g) := fun l => by
      have hl' := (hψ l).2.1
      rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl' _ hγ _).symm
    show ‖∑ l, ψ l (n.1 * g) - f (n.1 * g)‖ ≤ ε * 1
    rw [e1, Finset.sum_congr rfl fun l _ => e2 l, mul_one, norm_sub_rev]
    exact (happ _ ⟨_, hk, rfl⟩).le

end GlobalTheory.CuspLocApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IoYStOfIoPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem IoPair.of_index_eq {D : D7} (hP : IoPair D) (k : Fin D.R.m) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) (hC : ChainPar D k)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (hW : IsStepWeil k ψ V W ω) (hV : IsVacVec ψ θ M M' f)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (hJ : ∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f)
    (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (hν : ν.IsHaarMeasure)
    (h𝓕 : MeasureTheory.IsFundamentalDomain (GQ W) 𝓕 ν)
    (J' : Set (GA D W)) (χ' : GA D W → ℂ) (C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ)))
    (hle : C ≤ MultT θ M' J' χ') :
    Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ) := by
  subst ha hb
  exact hP k V W M M' θ ψ hθ hC ω f hW hV It hI J χ hJ ν 𝓕 hν h𝓕 J' χ' C hle

theorem ioYSt_of_ioPair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) (hL : LawsOK R)
    (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hkm : k < D.R.m := Nat.lt_of_succ_lt hk
  have hIt := hI
  have hInner := hν
  have hLast := hν'
  unfold RealDat.chain_ItY at hIt
  unfold RealDat.models_νY at hInner
  unfold RealDat.models_νY' at hLast

  have hmeas : (R.νY t (k + 1)).IsHaarMeasure ∧
      MeasureTheory.IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · exact ⟨(hInner t (k + 1) h2).1.1, (hInner t (k + 1) h2).2⟩
    · have atLast : ∀ j, j = D.R.m - 1 → (R.νY t j).IsHaarMeasure ∧
          MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
        rintro j rfl
        exact ⟨(hLast t).1.1, (hLast t).2⟩
      exact atLast (k + 1) (by omega)
  obtain ⟨hW, hV⟩ := hS.1 t ⟨k, hkm⟩ hk
  exact IoPair.of_index_eq hP ⟨k, hkm⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hkm.le)
    (min_eq_left hk.le) (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k)
    (R.vY t k) hW hV (R.ItY k) (hIt t k hk) _ _ (hL.1 t k hk) (R.νY t (k + 1)) (R.fdY t (k + 1))
    hmeas.1 hmeas.2 _ _ (R.CC t (k + 1)) le_rfl

end GlobalTheory.Chain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApproxAlt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspApproxCompact

theorem isCuspFun_of_approx (D : D7) (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g)
    (ha : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ : GA D V → ℂ, Continuous ψ ∧
      (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧ ∀ h ∈ C, ‖f h - ψ h‖ < δ) :
    IsCuspFun V f := by
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g := by
    have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    exact continuous_subtype_val.mul continuous_const
  have hC : IsCompact ((fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g) '' K) :=
    hK.image hcont
  have h1 := hint (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl) W hW μ hμ 𝓕 h𝓕 g
  have hfin : μ 𝓕 < ⊤ := by
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h | h
    · exact absurd h (by simp)
    · exact h
  have hM0 : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ ≤ δ * μ.real 𝓕 := by
    intro δ hδ
    obtain ⟨ψ, hψc, hψl, hψcusp, hψ⟩ := ha _ hC δ hδ
    have h0 := (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V ψ).1 hψcusp W hW μ hμ 𝓕 h𝓕 g
    have hfi := hint f hf hl W hW μ hμ 𝓕 h𝓕 g
    have hψi := hint ψ hψc hψl W hW μ hμ 𝓕 h𝓕 g
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm at h0 ⊢
    have e : ∫ n in 𝓕, f ((n : GA D V) * g) ∂μ = ∫ n in 𝓕, (f ((n : GA D V) * g) - ψ ((n : GA D V) * g)) ∂μ := by
      rw [integral_sub hfi hψi, h0, sub_zero]
    rw [e]
    refine norm_setIntegral_le_of_norm_le_const hfin fun n _ => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc n
    have hγ' : ((γ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) ∈ GQ V := by
      rw [GlobalTheory.AutFunCompare.GQ_eq]
      exact Subgroup.mem_subgroupOf.1 hγ
    have ee : f ((n : GA D V) * g) - ψ ((n : GA D V) * g) =
        f (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) -
          ψ (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hl _ hγ', hψl _ hγ']
    rw [ee]
    exact (hψ _ ⟨_, hk, rfl⟩).le
  by_contra hne
  have hpos : 0 < ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ := norm_pos_iff.2 hne
  have := key (‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ / (μ.real 𝓕 + 1)) (div_pos hpos (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at this
  nlinarith

end GlobalTheory.CuspApproxCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V), GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsDec Y X ι (fun _ : Fin 1 => z) (-GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.Tu D u) e f → ∀ L, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSDIn Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.flatSp Y X ι z) L → ∀ nn, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable nn → Formalism.IndefR.Datum.IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.lamN Y e f L nn)) := by
  first | exact @GlobalTheory.HypLattice.isSelfDualC_lamN | exact GlobalTheory.HypLattice.isSelfDualC_lamN | (intros; apply GlobalTheory.HypLattice.isSelfDualC_lamN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslatStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  first | exact @GlobalTheory.isMultiplicityInner_of_unit_twist_shift | exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift | (intros; apply GlobalTheory.isMultiplicityInner_of_unit_twist_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePow
section
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory.CoefHeight

open Polynomial

theorem val_coeff_prod_X_sub_C_le {K : Type} [Field K] (w : Valuation K ℝ≥0) {M : ℝ≥0} (hM : 1 ≤ M)
    (s : Multiset K) (hs : ∀ z ∈ s, w z ≤ M) (j : ℕ) :
    w ((s.map fun a => X - C a).prod.coeff j) ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    have ha : w a ≤ M := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ z ∈ s, w z ≤ M := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine (w.map_sub _ _).trans (max_le ?_ ?_)
    · cases j with
      | zero => rw [coeff_X_mul_zero, map_zero]; exact bot_le
      | succ i => rw [coeff_X_mul]; exact (ih hs' i).trans (pow_le_pow_right₀ hM (Nat.le_succ _))
    · rw [map_mul, pow_succ']
      exact mul_le_mul' ha (ih hs' j)

theorem nnnorm_coeff_minpoly_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ) :
    ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤
      max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set q := p.map (algebraMap F (FvBar F v)) with hqdef
  have hmon : q.Monic := (minpoly.monic hint).map _
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hq : q = (q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hmon
  have hroots : ∀ z ∈ q.roots, valBar F v z ≤ M := by
    intro z hz
    have hq0 : q ≠ 0 := hmon.ne_zero
    have hz' : aeval z p = 0 := by
      rw [mem_roots hq0, IsRoot, hqdef, eval_map_algebraMap] at hz; exact hz
    obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hz'
    have h1 : finEmb F v τ ((1 : v.adicCompletion F) ⊗ₜ[F] x) = z := by rw [finEmb_tmul, map_one, one_mul, hτ]
    show absBar F v z ≤ M
    rw [← h1]; exact (le_absFin F v τ _).trans (le_max_right _ _)
  have hcard : Multiset.card q.roots ≤ Module.finrank F E := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqdef, natDegree_map]; exact minpoly.natDegree_le x
  have key := val_coeff_prod_X_sub_C_le (valBar F v) hM q.roots hroots j
  rw [← hq] at key
  have hc : valBar F v (q.coeff j) = ‖algebraMap F (v.adicCompletion F) (p.coeff j)‖₊ := by
    show absBar F v _ = _
    rw [hqdef, coeff_map, IsScalarTower.algebraMap_apply F (v.adicCompletion F) (FvBar F v), absBar_algebraMap]
  rw [← hc]
  exact key.trans (pow_le_pow_right₀ hM hcard)

end GlobalTheory.CoefHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  first | exact @GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | exact GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | (intros; apply GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec <;> assumption)
end

