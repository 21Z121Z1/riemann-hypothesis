import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentMulMirabolicDetAverageEqZero
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg.Kill

theorem idem_eq_zero {G : Type} [Group G] [Fintype G] (E : MonoidAlgebra ℂ G) (h : E * E = E)
    (h1 : E.coeff 1 = 0) : E = 0 := by
  classical
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)
  haveI : Module.Free ℂ (MonoidAlgebra ℂ G) := Module.Free.of_basis (MonoidAlgebra.basis G ℂ)
  have hi : IsIdempotentElem (LinearMap.mulLeft ℂ E) := by
    refine LinearMap.ext fun x => ?_
    simp [← mul_assoc, h]
  have ht : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ E) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have : (MonoidAlgebra.basis G ℂ) x = MonoidAlgebra.single x 1 := by simp
    rw [this]
    show (E * MonoidAlgebra.single x 1).coeff x = 0
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp [h1]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi ht
  simpa using LinearMap.congr_fun h0 1

variable {G : Type} [Group G] [Fintype G]

theorem coeff_sum_single (F : G → ℂ) (x : G) :
    (∑ h : G, MonoidAlgebra.single h (F h)).coeff x = F x := by
  classical
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul' (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

def avg (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) : MonoidAlgebra ℂ G :=
  ∑ h : G, MonoidAlgebra.single h (if P h then χ h else 0)

theorem avg_coeff (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (x : G) :
    (avg P χ).coeff x = if P x then χ x else 0 :=
  coeff_sum_single _ x

theorem avg_mul_self (P : G → Prop) [DecidablePred P] (χ : G →* ℂ)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) :
    avg P χ * avg P χ = ((Finset.univ.filter P).card : ℂ) • avg P χ := by
  ext x
  rw [coeff_mul', MonoidAlgebra.coeff_smul_apply, avg_coeff, smul_eq_mul]
  have key : ∀ q, (avg P χ).coeff q * (avg P χ).coeff (q⁻¹ * x) = if P q then (if P x then χ x else 0) else 0 := by
    intro q
    simp only [avg_coeff]
    by_cases hq : P q
    · have hiff : P (q⁻¹ * x) ↔ P x := ⟨fun h => by simpa using hm _ _ hq h, fun h => hm _ _ (hi _ hq) h⟩
      by_cases hx : P x
      · rw [if_pos hq, if_pos (hiff.2 hx), if_pos hq, if_pos hx, ← map_mul, mul_inv_cancel_left]
      · rw [if_pos hq, if_neg (fun h => hx (hiff.1 h)), if_pos hq, if_neg hx, mul_zero]
    · rw [if_neg hq, if_neg hq, zero_mul]
  simp only [key]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem coeff_one_zOf_mul (ψ : G → ℂ) (a : MonoidAlgebra ℂ G) :
    (zOf ψ * a).coeff 1 = ψ 1 / (Fintype.card G : ℂ) * tr a ψ := by
  rw [coeff_mul', tr, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun q => ?_
  rw [zOf, coeff_sum_single]
  simp only [Equiv.inv_apply, inv_inv, mul_one]
  ring

theorem zOf_mul_avg_eq_zero (ψ : G → ℂ) (hψ : IsIrr ψ) (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (h1 : P 1)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) (htr : tr (avg P χ) ψ = 0) :
    zOf ψ * avg P χ = 0 := by
  obtain ⟨hid, hcen, -⟩ := GlobalTheory.GLq.ZOrth.zorth G ψ ψ hψ hψ
  rw [if_pos rfl] at hid
  set m := avg P χ with hmdef
  set n : ℂ := ((Finset.univ.filter P).card : ℂ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨1, by simp [h1]⟩
  have hmm : m * m = n • m := avg_mul_self P χ hm hi
  have hE : (n⁻¹ • (zOf ψ * m)) * (n⁻¹ • (zOf ψ * m)) = n⁻¹ • (zOf ψ * m) := by
    rw [smul_mul_smul_comm]
    have : zOf ψ * m * (zOf ψ * m) = n • (zOf ψ * m) := by
      calc zOf ψ * m * (zOf ψ * m) = zOf ψ * (m * zOf ψ) * m := by simp only [mul_assoc]
        _ = zOf ψ * (zOf ψ * m) * m := by rw [← hcen m]
        _ = (zOf ψ * zOf ψ) * (m * m) := by simp only [mul_assoc]
        _ = n • (zOf ψ * m) := by rw [hid, hmm, mul_smul_comm]
    rw [this, smul_smul, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
  have h1' : (n⁻¹ • (zOf ψ * m)).coeff 1 = 0 := by
    rw [MonoidAlgebra.coeff_smul_apply, coeff_one_zOf_mul, htr]
    simp
  have h0 := idem_eq_zero _ hE h1'
  rwa [smul_eq_zero, or_iff_right (inv_ne_zero hn0)] at h0

end GlobalTheory.MirAvg.Kill

namespace GlobalTheory.MirAvg

theorem mirSet_one {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) : mirSet a b (1 : Gn g r) := by
  cases b
  · intro x _; simp
  · intro x; exact ⟨0, by simp⟩

theorem mirSet_mul {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h h' : Gn g r)
    (hh : mirSet a b h) (hh' : mirSet a b h') : mirSet a b (h * h') := by
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh hh'
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh' x hx, hh x hx]
  · intro x
    simp only [mirSet, if_true] at hh hh'
    obtain ⟨c₂, hc₂⟩ := hh' x
    obtain ⟨c₁, hc₁⟩ := hh ((h' : Mt g r).mulVec x)
    refine ⟨c₁ + c₂, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, add_smul, ← hc₁, ← hc₂]
    abel

theorem mirSet_inv {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r)
    (hh : mirSet a b h) : mirSet a b h⁻¹ := by
  have hhi : ∀ x, (h : Mt g r).mulVec (((h⁻¹ : Gn g r) : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hih : ∀ x, ((h⁻¹ : Gn g r) : Mt g r).mulVec ((h : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh
    conv_lhs => rw [← hh x hx]
    exact hih x
  · intro x
    simp only [mirSet, if_true] at hh
    obtain ⟨c, hc⟩ := hh (((h⁻¹ : Gn g r) : Mt g r).mulVec x)
    refine ⟨-c, ?_⟩
    rw [hhi x] at hc
    rw [neg_smul, ← hc]
    abel

open Classical in

theorem zOf_mul_mirEl_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (r : ℕ) (ψ : Gn g r → ℂ), IsIrr ψ →
    ∀ (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g)
    (b : Bool), tr (mirEl θ a b) ψ = 0 → zOf ψ * mirEl θ a b = 0 := by
  intro g _ r ψ hψ θ a b htr
  let χ : Gn g r →* ℂ := (Units.coeHom ℂ).comp (θ.comp Matrix.GeneralLinearGroup.det)
  have hm : mirEl θ a b = Kill.avg (mirSet a b) χ := rfl
  rw [hm] at htr ⊢
  exact Kill.zOf_mul_avg_eq_zero ψ hψ (mirSet a b) χ (mirSet_one a b) (mirSet_mul a b) (mirSet_inv a b) htr

end GlobalTheory.MirAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Cocycle
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.ConnCoc

section General

variable {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem cocycle (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) (g h : G) :
    f (g * h) = f g + actT Y.L g (f h) := by
  apply Subtype.ext
  apply hι
  have e : ((f g + actT Y.L g (f h) : ↥Y.L.T) : Y.V) = (f g : Y.V) + Y.ρ g (f h : Y.V) := rfl
  rw [e, map_add, ι.equiv, hf, hf, hf, map_sub, map_mul, Module.End.mul_apply]
  abel

theorem continuous (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) :
    Continuous fun g => (f g : Y.V) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι.f (LinearMap.ker_eq_bot.2 hι)
  have : ContinuousSMul LL Y.V := IsModuleTopology.toContinuousSMul LL Y.V
  have hc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have e : (fun g => (f g : Y.V)) = fun g => r (Yt.ρ g yt) + (- r yt) := by
    funext g
    rw [← sub_eq_add_neg, ← map_sub, ← hf]
    exact (LinearMap.congr_fun hr _).symm
  rw [e]
  exact (hc.comp (Yt.cont yt)).add continuous_const

end General

theorem locConst {l : ℕ} [Fact l.Prime] {G V : Type} [TopologicalSpace G] [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] (T : Set V) {m : ℕ} (w : Module.Basis (Fin m) ℚ_[l] V)
    (hw : ∀ x : V, x ∈ T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) (hc : Continuous w.equivFun)
    (F : G → V) (hF : Continuous F) (n : ℕ) (g : G) :
    ∀ᶠ h in nhds g, ∃ y ∈ T, F h - F g = (l ^ n : ℕ) • y := by
  have hl : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ i, ∀ᶠ h in nhds g,
      ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ < 1 := by
    intro i
    have c : Continuous fun h =>
        ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ :=
      (continuous_const.mul (((continuous_apply i).comp (hc.comp hF)).sub continuous_const)).norm
    apply c.continuousAt.eventually_lt continuousAt_const
    simp
  filter_upwards [Filter.eventually_all.2 key] with h hh
  refine ⟨((l : ℚ_[l]) ^ n)⁻¹ • (F h - F g), (hw _).2 fun i => ?_, ?_⟩
  · have := (hh i).le
    simpa [Module.Basis.equivFun_apply] using this
  · rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, Nat.cast_pow, mul_inv_cancel₀ hl, one_smul]

theorem conn : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : FinExt l) (Y Yt : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom Y.L Yt.L), Function.Injective ι.f → ∀ (yt : Yt.V) (f : G → ↥Y.L.T), (∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) → (∀ g h, f (g * h) = f g + actT Y.L g (f h)) ∧ ∀ (n : ℕ) (g : G), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y := by
  intro l _ G _ _ LL Y Yt ι hι yt f hf
  refine ⟨cocycle Y Yt ι hι yt f hf, fun n g => ?_⟩
  obtain ⟨m, w, hw, hc, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l G LL Y
  have := locConst (Y.L.T : Set Y.V) w hw hc _ (continuous Y Yt ι hι yt f hf) n g
  filter_upwards [this] with h hh
  obtain ⟨y, hy, e⟩ := hh
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

end GlobalTheory.ConnCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_ring_integers_compact_adic_properties : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first | exact @GlobalTheory.GoodCoeff.good_coeff_integers | exact GlobalTheory.GoodCoeff.good_coeff_integers | (intros; apply GlobalTheory.GoodCoeff.good_coeff_integers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePowStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
section
noncomputable section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypePlaceCover

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [H.toHostAx.conjE_apply, H.toHostAx.conjE_apply, Complex.conj_conj]

def conjInt : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)

theorem conjInt_coe (x : 𝓞 H.E) : (conjInt H x : H.E) = H.conj x := rfl

theorem conjInt_conjInt (x : 𝓞 H.E) : conjInt H (conjInt H x) = x :=
  RingOfIntegers.ext (by rw [conjInt_coe, conjInt_coe, conj_conj])

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  ⟨w.asIdeal.comap (conjInt H), haveI := w.isPrime; Ideal.comap_isPrime _ _, fun h0 => w.ne_bot (by
    rw [eq_bot_iff]
    intro x hx
    have : conjInt H x ∈ w.asIdeal.comap (conjInt H) := by rwa [Ideal.mem_comap, conjInt_conjInt]
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjInt_conjInt H x, this, map_zero])⟩

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (conjPl H w).asIdeal ↔ conjInt H x ∈ w.asIdeal := Iff.rfl

theorem conjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : conjPl H (conjPl H w) = w :=
  HeightOneSpectrum.ext (by ext x; rw [mem_conjPl, mem_conjPl, conjInt_conjInt])

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hxy
  have : y = conjInt H x := RingOfIntegers.ext hxy
  rw [mem_conjPl, this, conjInt_conjInt]

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show conjInt H _ ∈ w.asIdeal
  rw [map_natCast]; exact hw

theorem finrank_eq : Module.finrank ℚ H.E = 2 * R.f := by
  have h1 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have h5 : R.f = 2 * R.ord := rfl
  rw [h1, h5]; ring

theorem place_cover : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  intro D k w hw
  have hne : ∀ v v' : D.nd.PlG k, D.naut.plGw k v ≠ conjPl D.host (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_conjPl _ _)
  let f : D.nd.PlG k ⊕ D.nd.PlG k → placesOver D.host.E (D.host.g k) :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, D.naut.plGw_over k v⟩)
      fun v => ⟨conjPl D.host (D.naut.plGw k v), conjPl_mem_placesOver _ (D.naut.plGw_over k v)⟩
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · rw [D.naut.plGw_inj k e']
    · exact absurd e' (hne a b)
    · exact absurd e'.symm (hne b a)
    · have := congrArg (conjPl D.host) e'
      simp only [f, Sum.elim_inr, conjPl_conjPl] at this
      rw [D.naut.plGw_inj k this]
  have hc : Nat.card (placesOver D.host.E (D.host.g k)) = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, D.nd.g_split k, finrank_eq, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite (placesOver D.host.E (D.host.g k)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, D.nd.g_split k]
    exact Module.finrank_pos.ne'
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · refine ⟨v, Or.inr ?_⟩
    have e : conjPl D.host (D.naut.plGw k v) = w := congrArg Subtype.val hx
    exact e ▸ isConjPl_conjPl _ _

end GlobalTheory.TypePlaceCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem continuous_charpoly_coeff_of_matrix {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by

  have key : ∀ M : Matrix (Fin n) (Fin n) K, M.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := fun M =>
    (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K)
      (fun p : Fin n × Fin n => M p.1 p.2) i).symm
  have hfun : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := funext key
  rw [hfun]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

theorem charpoly_eq_of_dense :
    ∀ (Γ : Type) [TopologicalSpace Γ] (K : Type) [CommRing K] [TopologicalSpace K]
      [IsTopologicalRing K] [T2Space K] (n : ℕ) (a b : Γ → Matrix (Fin n) (Fin n) K) (S : Set Γ),
      Dense S → Continuous a → Continuous b → (∀ g ∈ S, (a g).charpoly = (b g).charpoly) →
      ∀ g, (a g).charpoly = (b g).charpoly := by
  intro Γ _ K _ _ _ _ n a b S hS ha hb hab g

  ext i
  have hc : ∀ c : Γ → Matrix (Fin n) (Fin n) K, Continuous c →
      Continuous fun x => (c x).charpoly.coeff i :=
    fun c hc => (continuous_charpoly_coeff_of_matrix n i).comp hc
  have heq := Continuous.ext_on hS (hc a ha) (hc b hb) (fun x hx => by simp only [hab x hx])
  exact congrFun heq g

end GlobalTheory.TypeLeaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupportStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  first | exact @GlobalTheory.Cut.value_mem_ccOff | exact GlobalTheory.Cut.value_mem_ccOff | (intros; apply GlobalTheory.Cut.value_mem_ccOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTowerStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_action_on_root_tower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) → ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  first | exact @GlobalTheory.ExpImage.actT_εroot_eq_pow | exact GlobalTheory.ExpImage.actT_εroot_eq_pow | (intros; apply GlobalTheory.ExpImage.actT_εroot_eq_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEllStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_unramified_away_from_ell : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  first | exact @GlobalTheory.CycUnram.main | exact GlobalTheory.CycUnram.main | (intros; apply GlobalTheory.CycUnram.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithfulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  first | exact @GlobalTheory.TiltFaithful.faithH | exact GlobalTheory.TiltFaithful.faithH | (intros; apply GlobalTheory.TiltFaithful.faithH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroupsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  first | exact @GlobalTheory.Cyc.Decomp.grp_GKs_H | exact GlobalTheory.Cyc.Decomp.grp_GKs_H | (intros; apply GlobalTheory.Cyc.Decomp.grp_GKs_H <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem cyc_eq_binomialSeries (c : ℤ_[l]) : cyc l O c = PowerSeries.binomialSeries O c - 1 := by
  rw [cyc, GlobalTheory.Fon.map_binomialSeries _ (fun _ => rfl)]

theorem act_X (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := PowerSeries.substAlgHom_X _

theorem act_apply (c : ℤ_[l]) (a : PowerSeries O) :
    act l O c a = PowerSeries.subst (cyc l O c) a :=
  congrFun (PowerSeries.coe_substAlgHom _) a

theorem act_eq_gam (c : ℤ_[l]) : act l O c = GlobalTheory.Fon.gam O c :=
  GlobalTheory.Fon.algHom_ext_X (by rw [act_X, GlobalTheory.Fon.gam_X, cyc_eq_binomialSeries])
    (by rw [act_X, cyc_const])

theorem act_act (c c' : ℤ_[l]) (a : PowerSeries O) :
    act l O c (act l O c' a) = act l O (c * c') a := by
  simp only [act_eq_gam, GlobalTheory.Fon.gam_mul]

theorem act_one (a : PowerSeries O) : act l O 1 a = a := by
  rw [act_eq_gam, GlobalTheory.Fon.gam_one]

theorem cyc_natCast (k : ℕ) : cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1 := by
  rw [cyc_eq_binomialSeries, PowerSeries.binomialSeries_nat]

theorem coeff_one_cyc (c : ℤ_[l]) : PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c := by
  rw [cyc_eq_binomialSeries, ← GlobalTheory.Fon.gam_X, GlobalTheory.Fon.coeff_one_gam_X]

theorem act_pow_sub_one (c : ℤ_[l]) (k : ℕ) :
    act l O c ((1 + PowerSeries.X) ^ k - 1) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  rw [← cyc_natCast l O k, ← act_apply, ← act_X l O c, ← act_X l O (k : ℤ_[l]), act_act, act_act,
    mul_comm]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) :=
  fun l _ O _ _ => ⟨act_X l O, act_act l O, act_one l O, cyc_natCast l O, coeff_one_cyc l O,
    act_pow_sub_one l O⟩

end GlobalTheory.Cyc
end
end

