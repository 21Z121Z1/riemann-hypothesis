import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalarStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0010

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace PositivityTheory.ThKF0.Sg

section Split

variable {F A R₁ R₂ : Type} (E : Type) [Field F] [CommRing A] [Algebra F A] [CommRing R₁] [Algebra F R₁] [CommRing R₂]
  [Algebra F R₂] [CommRing E] [Algebra F E]

def split (s : A ≃ₐ[F] R₁ × R₂) : A ⊗[F] E ≃ₐ[F] (R₁ ⊗[F] E) × (R₂ ⊗[F] E) :=
  (Algebra.TensorProduct.congr s AlgEquiv.refl).trans
    (((Algebra.TensorProduct.comm F (R₁ × R₂) E).trans (Algebra.TensorProduct.prodRight F F E R₁ R₂)).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm F E R₁) (Algebra.TensorProduct.comm F E R₂)))

variable {E}

theorem split_tmul (s : A ≃ₐ[F] R₁ × R₂) (a : A) (e : E) :
    split E s (a ⊗ₜ[F] e) = ((s a).1 ⊗ₜ[F] e, (s a).2 ⊗ₜ[F] e) := by
  have h : (Algebra.TensorProduct.comm F (R₁ × R₂) E) (s a ⊗ₜ[F] e) = e ⊗ₜ[F] s a := rfl
  have h0 : Algebra.TensorProduct.congr s (AlgEquiv.refl : E ≃ₐ[F] E) (a ⊗ₜ[F] e) = s a ⊗ₜ[F] e := rfl
  simp only [split, AlgEquiv.trans_apply, h0, h, Algebra.TensorProduct.prodRight_tmul]
  rfl

theorem split_conj (s : A ≃ₐ[F] R₁ × R₂) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    split E s (Algebra.TensorProduct.map (AlgHom.id A A) σ x) =
      (Algebra.TensorProduct.map (AlgHom.id F R₁) σ (split E s x).1,
        Algebra.TensorProduct.map (AlgHom.id F R₂) σ (split E s x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, split_tmul, split_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    simp

end Split

section Piece

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {c : S →ₐ[R] S} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mix_mul {f : S} (hf : f * f = f) (A B C D : Matrix ι ι S) :
    (f • A + (1 - f) • B) * (f • C + (1 - f) • D) = f • (A * C) + (1 - f) • (B * D) := by
  have h1 : f * (1 - f) = 0 := by linear_combination -hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hf, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_self (f : S) (A : Matrix ι ι S) : f • A + (1 - f) • A = A := by
  rw [← add_smul, add_sub_cancel, one_smul]

def piece {J : Matrix ι ι S} {f : S} (hf : f * f = f) (hc : c f = f) (g : UG c J) : UG c J :=
  ⟨⟨f • g.1.1 + (1 - f) • 1, f • (g.1⁻¹).1 + (1 - f) • 1, by rw [mix_mul hf, Units.mul_inv, mul_one, mix_self],
    by rw [mix_mul hf, Units.inv_mul, mul_one, mix_self]⟩, by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    change (f • g.1.1 + (1 - f) • 1)ᵀ * J * (f • g.1.1 + (1 - f) • (1 : Matrix ι ι S)).map c = J
    have e : (f • g.1.1 + (1 - f) • (1 : Matrix ι ι S)).map c = f • (g.1.1).map c + (1 - f) • 1 := by
      ext i j
      by_cases h : i = j <;> simp [hc, Matrix.one_apply, h]
    rw [e, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
    have k : ∀ A B : Matrix ι ι S, (f • A + (1 - f) • 1) * J * (f • B + (1 - f) • 1) = f • (A * J * B) + (1 - f) • J :=
      fun A B => by
        conv_lhs => rw [← mix_self f J]
        rw [mix_mul hf, mix_mul hf, one_mul, mul_one]
    rw [k, hg, mix_self]⟩

end Piece

variable {F : Type} [Field F] [NumberField F]

open GlobalTheory.LocalGlobalChar

variable (F) in

abbrev RS (S : Finset (HeightOneSpectrum (𝓞 F))) : Type := Ainf F × ((v : S) → Fv F v.1)

def toRS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F →ₐ[F] RS F S :=
  (AlgHom.fst F (Ainf F) (Af F)).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (AlgHom.snd F (Ainf F) (Af F)))

theorem toRS_eps (S : Finset (HeightOneSpectrum (𝓞 F))) : toRS S (eps S) = 1 := by
  refine Prod.ext rfl (funext fun v => ?_)
  change evalV F v.1 (ind S) = 1
  rw [ev_ind, if_pos v.2]

theorem eps_mul_of (S : Finset (HeightOneSpectrum (𝓞 F))) {a : AF F} (h : toRS S a = 0) : eps S * a = 0 := by
  have h1 : a.1 = 0 := congrArg Prod.fst h
  refine Prod.ext ?_ (fin_ext fun u => ?_)
  · change 1 * a.1 = 0
    rw [h1, mul_zero]
  · change evalV F u (ind S * a.2) = evalV F u 0
    rw [map_mul, ev_ind, map_zero]
    split_ifs with hu
    · have h2 : evalV F u a.2 = 0 := congrFun (congrArg Prod.snd h) ⟨u, hu⟩
      rw [h2, mul_zero]
    · rw [zero_mul]

theorem toRS_surj (S : Finset (HeightOneSpectrum (𝓞 F))) : Function.Surjective (toRS S) := by
  classical
  intro r
  let y : Af F := ⟨fun u => if h : u ∈ S then r.2 ⟨u, h⟩ else 0, by
    refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
    beta_reduce
    rw [dif_neg hvS']
    exact zero_mem (v.adicCompletionIntegers F)⟩
  refine ⟨pairA F r.1 y, Prod.ext rfl (funext fun v => ?_)⟩
  exact dif_pos v.2

def splitS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F ≃ₐ[F] RS F S × (AF F ⧸ Ideal.span {eps S}) :=
  AlgEquiv.ofBijective ((toRS S).prod (Ideal.Quotient.mkₐ F _)) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h1 : toRS S a = 0 := congrArg Prod.fst ha
    have h2 : Ideal.Quotient.mk (Ideal.span {eps S}) a = 0 := congrArg Prod.snd ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    have h3 := eps_mul_of S h1
    rwa [mul_left_comm, eps_mul_self] at h3, by
    rintro ⟨r, q⟩
    obtain ⟨a, rfl⟩ := toRS_surj S r
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h0 : Ideal.Quotient.mk (Ideal.span {eps S}) (eps S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    refine ⟨eps S * a + (1 - eps S) * b, Prod.ext ?_ ?_⟩
    · change toRS S _ = toRS S a
      rw [map_add, map_mul, map_mul, map_sub, map_one, toRS_eps]
      ring
    · change Ideal.Quotient.mk (Ideal.span {eps S}) _ = Ideal.Quotient.mk (Ideal.span {eps S}) b
      rw [map_add, map_mul, map_mul, map_sub, map_one, h0]
      ring⟩

theorem splitS_eps (S : Finset (HeightOneSpectrum (𝓞 F))) : (splitS S (eps S)).2 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem triv_piece (hσ : IsCMExt F E σ) {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β (AE F E)) (hJ : IsUnit J.det)
    (lam : UG (cA σ) (dbl J) →* ℂˣ)
    (h : ∀ (p : UG (cA σ) (dbl J)) (t : GL β (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols β = diagCols β * t.1 → lam p = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g : UG (cA σ) (dbl J))
    (hg : ∀ i j, ∃ y, (g.1.1 - 1 : Matrix _ _ (AE F E)) i j = algebraMap (AF F) (AE F E) (eps S) * y) : lam g = 1 := by
  obtain ⟨x, hx⟩ := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.exists_moved hσ
  have hi := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.sigma_invol hσ
  have hξ : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)
  have : IsArtinianRing (Ainf F) := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.isArtinian_inf
  have : IsArtinianRing (RS F S ⊗[F] E) := IsArtinianRing.of_finite (RS F S) _
  refine GlobalTheory.T.hermitian_darboux_split_product F (AF F) (AE F E) (RS F S ⊗[F] E) ((AF F ⧸ Ideal.span {eps S}) ⊗[F] E) (cA σ)
    (Algebra.TensorProduct.map (AlgHom.id F _) σ) (Algebra.TensorProduct.map (AlgHom.id F _) σ).toRingHom
    (1 ⊗ₜ[F] (x - σ x)) (split E (splitS S)).toRingEquiv ?_ ?_ (fun z => ?_)
    (fun z => congrArg Prod.fst (split_conj (splitS S) σ z)) (fun z => congrArg Prod.snd (split_conj (splitS S) σ z))
    β J hJ lam (fun p t _ _ hpt => h p t hpt) g fun i j => ?_
  · refine IsUnit.of_mul_eq_one ((1 : RS F S) ⊗ₜ[F] (x - σ x)⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hξ]
    rfl
  · rw [Algebra.TensorProduct.map_tmul, map_sub, hi, ← TensorProduct.tmul_neg, neg_sub]
    rfl
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hi]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · obtain ⟨y, hy⟩ := hg i j
    change (split E (splitS S) ((g.1.1 - 1 : Matrix _ _ (AE F E)) i j)).2 = 0
    have e : algebraMap (AF F) (AE F E) (eps S) = eps S ⊗ₜ[F] (1 : E) := rfl
    rw [hy, map_mul, Prod.snd_mul, e, split_tmul, splitS_eps, TensorProduct.zero_tmul, zero_mul]

theorem tendsto_mix' {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AE F E) (eps S) • M +
      (1 - algebraMap (AF F) (AE F E) (eps S)) • (1 : Matrix ι ι (AE F E))) atTop (𝓝 M) := by
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.ThKF0.Sg

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
theorem PositivityTheory.ThKF0.local_global_character_interpolation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  have he : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), algebraMap (AF F) (AE F E) (eps S) * algebraMap (AF F) (AE F E) (eps S) =
      algebraMap (AF F) (AE F E) (eps S) := fun S => by rw [← map_mul, eps_mul_self]
  refine ⟨fun S => piece (he S) ((cA σ).commutes _) g, fun S => rfl, ?_⟩
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact (tendsto_mix' g.1.1).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_mix' (g.1⁻¹).1))

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
theorem PositivityTheory.ThKF0.parabolic_character_trivial_on_diagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1 := by
  intro F E _ _ _ _ _ σ hσ n J ε _ hdet c hc hP
  have hJ : IsUnit (incM F J).det := by
    have h := (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at h
  refine MonoidHom.ext fun g => ?_
  obtain ⟨q, hq, hlim⟩ := PositivityTheory.ThKF0.local_global_character_interpolation F E σ (dbl (incM F J)) g
  have h1 : ∀ S, c (q S) = 1 := fun S => triv_piece hσ _ hJ c hP S (q S) fun i j =>
    ⟨(g.1.1 - 1 : Matrix _ _ (AE F E)) i j, by
      rw [hq S]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring⟩
  have h2 : Tendsto (fun S => c (q S)) atTop (𝓝 (c g)) := (hc.tendsto g).comp hlim
  simp only [h1] at h2
  exact (tendsto_nhds_unique tendsto_const_nhds h2).symm

end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem isStd_ne_one (hψ : IsStd ψ) : ψ ≠ 1 := by
  intro h1
  have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have e := GlobalTheory.PsiNontriv.isStd_fin_rat hψ (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))
  rw [h1, AddChar.one_apply, Algebra.trace_algebraMap] at e
  have e2 : (Module.finrank ℚ F • (1 / (2 * (Module.finrank ℚ F : ℚ))) : ℚ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [e2] at e
  have e3 : 2 * (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℚ)) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [e3, Complex.exp_pi_mul_I] at e
  norm_num at e

variable (F) in

def ratPt (y z : κ → F) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

section One

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

structure Tw (ψ : AddChar (AF F) ℂ) (d d₁ : Darboux B κ) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  maps : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, e (d.rho ψ w Φ) = d₁.rho ψ w (e Φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ
  ne : ∃ Φ ∈ schA F κ, e Φ ≠ 0

def RatRel (d d₁ : Darboux B κ) : Prop := ∀ y z : κ → F, ∃ w y' z', d.e w = ratPt F y z ∧ d₁.e w = ratPt F y' z'

variable {d d₁ d₂ : Darboux B κ} {e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem rho_mem (hψ : IsStd ψ) (d : Darboux B κ) (w : W) {Φ} (hΦ : Φ ∈ schA F κ) : d.rho ψ w Φ ∈ schA F κ :=
  (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1 _ Φ hΦ

theorem eq_zero_of_theta (hψ : IsStd ψ) (d : Darboux B κ) {Φ} (hΦ : Φ ∈ schA F κ) (h : ∀ w, thetaSum F (d.rho ψ w Φ) = 0) :
    Φ = 0 :=
  GlobalTheory.T.theta_heisenberg_translates_separate F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 Φ hΦ fun w => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h w'

theorem rho_smul (d : Darboux B κ) (w : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : d.rho ψ w (c • Φ) = c • d.rho ψ w Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_sub (d : Darboux B κ) (w : W) (Φ Ψ : (κ → AF F) → ℂ) : d.rho ψ w (Φ - Ψ) = d.rho ψ w Φ - d.rho ψ w Ψ := by
  funext x
  simp only [Darboux.rho, schr, Pi.sub_apply]
  ring

theorem eq_of_theta (hψ : IsStd ψ) (d : Darboux B κ) {Φ Ψ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ)
    (h : ∀ w, thetaSum F (d.rho ψ w Φ) = thetaSum F (d.rho ψ w Ψ)) : Φ = Ψ := by
  obtain ⟨-, ⟨l, -, hl⟩, -⟩ := GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  refine sub_eq_zero.1 (eq_zero_of_theta hψ d (sub_mem hΦ hΨ) fun w => ?_)
  rw [← hl _ (rho_mem hψ d w (sub_mem hΦ hΨ)), rho_sub, map_sub, hl _ (rho_mem hψ d w hΦ), hl _ (rho_mem hψ d w hΨ), h, sub_self]

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem Tw.theta (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := by
  obtain ⟨-, ⟨l, hl0, hl⟩, -⟩ := GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  have hinv := (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).2
  obtain ⟨a, ha⟩ := GlobalTheory.T.admissible_functional_rational_invariance F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 (l ∘ₗ e) (h.adm l hl0) fun w Φ hΦ => by
    obtain ⟨u, y', z', h1, h2⟩ := hr w.1 w.2
    have e1 := h.Heisenberg₂ u Φ hΦ
    rw [Darboux.rho, Darboux.rho, h1, h2] at e1
    have e2 := rho_mem hψ d₁ u (h.maps Φ hΦ)
    rw [Darboux.rho, h2] at e2
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine (congrArg l e1).trans ?_
    rw [hl _ e2, hl _ (h.maps Φ hΦ)]
    exact hinv (y', z') _
  have ha' : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = a * thetaSum F Φ := fun Φ hΦ => by
    rw [← ha Φ hΦ, LinearMap.comp_apply, hl _ (h.maps Φ hΦ)]
  refine ⟨a, fun a0 => ?_, ha'⟩
  obtain ⟨Φ, hΦ, hne⟩ := h.ne
  refine hne (eq_zero_of_theta hψ d₁ (h.maps Φ hΦ) fun w => ?_)
  rw [← h.Heisenberg₂ w Φ hΦ, ha' _ (rho_mem hψ d w hΦ), a0, zero_mul]

theorem Tw.inj (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) {Φ} (hΦ : Φ ∈ schA F κ) (h0 : e Φ = 0) : Φ = 0 := by
  obtain ⟨c, hc, H⟩ := h.theta hψ hr
  refine eq_zero_of_theta hψ d hΦ fun w => ?_
  have := H _ (rho_mem hψ d w hΦ)
  rw [h.Heisenberg₂ w Φ hΦ, h0, ← zero_smul ℂ (0 : (κ → AF F) → ℂ), rho_smul, thetaSum_smul, zero_mul] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hc

theorem schur (hψ : IsStd ψ) (d : Darboux B κ) (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d.rho ψ w (T Φ)) : ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ :=
  GlobalTheory.T.heisenberg_commuting_operator_scalar F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 T h1 h2 fun w Φ hΦ => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h3 w' Φ hΦ

theorem Tw.smul (h : Tw ψ d d₁ e) {c : ℂ} (hc : c ≠ 0) : Tw ψ d d₁ (c • e) where
  maps Φ hΦ := Submodule.smul_mem _ c (h.maps Φ hΦ)
  Heisenberg₂ w Φ hΦ := by rw [LinearMap.smul_apply, LinearMap.smul_apply, h.Heisenberg₂ w Φ hΦ, rho_smul]
  adm l hl g hg := by
    obtain ⟨T, hT⟩ := h.adm l hl g hg
    refine ⟨c • T, fun f => ?_⟩
    rw [LinearMap.comp_smul, LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]
  ne := by
    obtain ⟨Φ, hΦ, h0⟩ := h.ne
    exact ⟨Φ, hΦ, smul_ne_zero hc h0⟩

theorem Tw.exists_inv (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (h' : Tw ψ d₁ d e') (hr : RatRel d d₁) (hr' : RatRel d₁ d) :
    ∃ e'', Tw ψ d₁ d e'' ∧ (∀ Φ ∈ schA F κ, e'' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e'' Φ) = Φ := by
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h.ne
    exact hne (h'.inj hψ hr' (h.maps Φ hΦ) ((ha Φ hΦ).trans (by rw [a0, zero_smul])))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  have h'' := h'.smul (inv_ne_zero a0)
  refine ⟨_, h'', h1, fun Φ hΦ => sub_eq_zero.1 (h''.inj hψ hr' (sub_mem (h.maps _ (h''.maps Φ hΦ)) hΦ) ?_)⟩
  rw [map_sub, h1 _ (h''.maps Φ hΦ), sub_self]

def negD (d : Darboux B κ) : Darboux (fun w w' => -B w w') κ where
  e := d.e.trans ((LinearEquiv.refl _ _).prodCongr (LinearEquiv.neg _))
  form w w' := by
    rw [d.form]
    simp
    ring

theorem negD_e (d : Darboux B κ) (w : W) : (negD d).e w = ((d.e w).1, -(d.e w).2) := rfl

theorem RatRel.neg (hr : RatRel d d₁) : RatRel (negD d) (negD d₁) := fun y z => by
  obtain ⟨w, y', z', h1, h2⟩ := hr y (-z)
  refine ⟨w, y', -z', ?_, ?_⟩
  · rw [negD_e, h1]; simp [ratPt, funext_iff]
  · rw [negD_e, h2]; simp [ratPt, funext_iff]

end One

def TwEx : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F) (d d₁ : Darboux B κ), ∃ e, Tw ψ d d₁ e

theorem schr_box {κ' : Type} [Fintype κ'] (a b : κ → AF F) (a' b' : κ' → AF F) (φ : (κ → AF F) → ℂ) (φ' : (κ' → AF F) → ℂ) :
    schr ψ (Sum.elim a a', Sum.elim b b') (boxFun φ φ') = boxFun (schr ψ (a, b) φ) (schr ψ (a', b') φ') := by
  funext x
  have e1 : (x + Sum.elim a a') ∘ Sum.inl = x ∘ Sum.inl + a := rfl
  have e2 : (x + Sum.elim a a') ∘ Sum.inr = x ∘ Sum.inr + a' := rfl
  have e3 : x ⬝ᵥ Sum.elim b b' + ⅟(2 : AF F) * (Sum.elim a a' ⬝ᵥ Sum.elim b b') =
      (x ∘ Sum.inl ⬝ᵥ b + ⅟(2 : AF F) * (a ⬝ᵥ b)) + (x ∘ Sum.inr ⬝ᵥ b' + ⅟(2 : AF F) * (a' ⬝ᵥ b')) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [schr, boxFun, e1, e2, e3, AddChar.map_add_eq_mul]
  ring

section Dbl

variable {E : Type} [CommRing E] [Algebra (AF F) E] {c : E →ₐ[AF F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
  {dd dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}

theorem RatRel.dbl (hr : RatRel d d₁) (h : IsDblCoord c ξ JA JB d dd) (h₁ : IsDblCoord c ξ JA JB d₁ dd₁) : RatRel dd dd₁ := by
  intro y z
  obtain ⟨w, y', z', h1, h2⟩ := hr (y ∘ Sum.inl) (z ∘ Sum.inl)
  obtain ⟨u, y'', z'', h3, h4⟩ := hr (y ∘ Sum.inr) (-z ∘ Sum.inr)
  refine ⟨Matrix.fromCols w u, Sum.elim y' y'', Sum.elim z' (-z''), ?_, ?_⟩
  · rw [h, h1, h3]
    ext (i | i) <;> simp [ratPt]
  · rw [h₁, h2, h4]
    ext (i | i) <;> simp [ratPt]

theorem rho_box (h : IsDblCoord c ξ JA JB d dd) (w u : Matrix α β E) (φ φ' : (κ → AF F) → ℂ) :
    dd.rho ψ (Matrix.fromCols w u) (boxFun φ φ') = boxFun (d.rho ψ w φ) ((negD d).rho ψ u φ') := by
  rw [Darboux.rho, h, schr_box]
  rfl

theorem box_compat (hT : TwEx) (hψ : IsStd ψ) (hr : RatRel d d₁) (h : IsDblCoord c ξ JA JB d dd)
    (h₁ : IsDblCoord c ξ JA JB d₁ dd₁) {e ed} (he : Tw ψ d d₁ e) (hd : Tw ψ dd dd₁ ed) :
    ∃ e₂, Tw ψ (negD d) (negD d₁) e₂ ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ed (boxFun φ φ') = boxFun (e φ) (e₂ φ') := by
  obtain ⟨e₀, h₀⟩ := hT F ψ hψ κ _ _ (negD d) (negD d₁)
  obtain ⟨a, ha, Ha⟩ := he.theta hψ hr
  obtain ⟨b, hb, Hb⟩ := h₀.theta hψ hr.neg
  obtain ⟨t, ht, Ht⟩ := hd.theta hψ (hr.dbl h h₁)
  have h₂ := h₀.smul (div_ne_zero ht (mul_ne_zero ha hb))
  refine ⟨_, h₂, fun φ hφ φ' hφ' => ?_⟩
  have hb1 := (GlobalTheory.T.theta_sum_tensor_product F κ κ φ hφ φ' hφ').1
  refine eq_of_theta hψ dd₁ (hd.maps _ hb1) (GlobalTheory.T.theta_sum_tensor_product F κ κ _ (he.maps φ hφ) _ (h₂.maps φ' hφ')).1 fun w => ?_
  rw [← Matrix.fromCols_toCols w]
  generalize w.toCols₁ = u
  generalize w.toCols₂ = u'
  have m1 := rho_mem hψ d u hφ
  have m2 := rho_mem hψ (negD d) u' hφ'
  rw [← hd.Heisenberg₂ _ _ hb1, Ht _ (rho_mem hψ dd _ hb1), rho_box h, rho_box h₁, (GlobalTheory.T.theta_sum_tensor_product F κ κ _ m1 _ m2).2,
    ← he.Heisenberg₂ u φ hφ, ← h₂.Heisenberg₂ u' φ' hφ', (GlobalTheory.T.theta_sum_tensor_product F κ κ _ (he.maps _ m1) _ (h₂.maps _ m2)).2, Ha _ m1,
    LinearMap.smul_apply, thetaSum_smul, Hb _ m2]
  field_simp

end Dbl

end PositivityTheory.ThKF0

end
end

