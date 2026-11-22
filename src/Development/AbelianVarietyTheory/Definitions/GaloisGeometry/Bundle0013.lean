import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Formalism.LocalToGlobal.HermitianForms.Bundle0005
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FracZeroOfPos
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {d : ℕ}

def pw (f : Fin d → R) : Submonoid R := Submonoid.powers (∏ j, f j)

def omitted (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Submodule R (LocalizedModule (pw f) M) :=
  Submodule.span R {z | ∃ (j : Fin d) (k : ℕ) (m : M), z = LocalizedModule.mk (f j ^ k • m) ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩}

abbrev LC (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Type :=
  LocalizedModule (pw f) M ⧸ omitted f M

def frac (f : Fin d → R) {M : Type} [AddCommGroup M] [Module R M] (m : M) (k : ℕ) : LC f M :=
  Submodule.Quotient.mk (LocalizedModule.mk m ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩)

theorem frac_surjective (f : Fin d → R) (x : LC f M) : ∃ (m : M) (k : ℕ), x = frac f m k := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction y using LocalizedModule.induction_on with
  | h m u =>
    obtain ⟨k, hk⟩ := u.2
    refine ⟨m, k, ?_⟩
    unfold frac
    congr 2
    exact Subtype.ext hk.symm

theorem frac_prod_smul (f : Fin d → R) (m : M) (k : ℕ) : frac f ((∏ l, f l) • m) (k + 1) = frac f m k := by
  unfold frac
  congr 1
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_succ]

theorem frac_zero_of_pos (f : Fin d → R) (hd : 0 < d) (m : M) : frac f m 0 = 0 := by
  unfold frac
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨⟨0, hd⟩, 0, m, by simp⟩

def IsRes {B : Type} [CommRing B] [Algebra ℂ B] (s : Fin d → B) (e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ)
    (ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ) : Prop :=
  (∀ j, e (s j) = MvPowerSeries.X j) ∧
  (∀ ω : Om ℂ B d, ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) ∧
  ∀ (k : ℕ) (h : B), ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h)

namespace IsRes

variable {B : Type} [CommRing B] [Algebra ℂ B] {s : Fin d → B} {e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ}
  {ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ}

theorem top_form (hρ : IsRes s e ρ) (ω : Om ℂ B d) :
    ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j) := hρ.2.1 ω

theorem apply_frac (hρ : IsRes s e ρ) (k : ℕ) (h : B) :
    ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h) := hρ.2.2 k h

theorem unique {ρ' : LC s (Om ℂ B d) →ₗ[ℂ] ℂ} (hρ : IsRes s e ρ) (hρ' : IsRes s e ρ') : ρ = ρ' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨ω, k, rfl⟩ := frac_surjective s x
  rw [← frac_prod_smul s ω k]
  obtain ⟨h, hh⟩ := hρ.top_form ((∏ l, s l) • ω)
  rw [hh, hρ.apply_frac, hρ'.apply_frac]

end IsRes

end GlobalTheory.W1

namespace GlobalTheory.W1.Ex

def rho0 (s : Fin 0 → ℂ) : LC s (Om ℂ ℂ 0) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ (omitted s (Om ℂ ℂ 0))
    ((exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).toLinearMap ∘ₗ
      LocalizedModule.lift (pw s) LinearMap.id (fun u => by
        obtain ⟨n, hn⟩ := u.2
        have : (u : ℂ) = 1 := by simpa using hn.symm
        rw [this, map_one]; exact isUnit_one))
    (by
      have : omitted s (Om ℂ ℂ 0) = ⊥ := by
        unfold omitted
        rw [Submodule.span_eq_bot]
        rintro z ⟨j, _, _, _⟩
        exact j.elim0
      rw [this]; exact bot_le))

example (s : Fin 0 → ℂ) : IsRes s (Algebra.ofId ℂ (MvPowerSeries (Fin 0) ℂ)) (rho0 s) := by
  refine ⟨fun j => j.elim0, fun ω => ⟨exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ] ω, ?_⟩, fun k h => ?_⟩
  · apply (exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).injective
    rw [LinearEquiv.map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  · have hn : (Finsupp.equivFunOnFinite.symm fun _ : Fin 0 => k) = 0 := Subsingleton.elim _ _
    rw [hn, Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.coeff_zero_C]
    simp [rho0, frac, LocalizedModule.lift_mk, exteriorPower.zeroEquiv_ιMulti]

example : frac (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (1 : Polynomial ℂ) 0 = 0 :=
  frac_zero_of_pos _ Nat.one_pos _

example : frac (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (Polynomial.X : Polynomial ℂ) 2 =
    frac (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (1 : Polynomial ℂ) 1 := by
  have := frac_prod_smul (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (1 : Polynomial ℂ) 1
  simpa using this

end GlobalTheory.W1.Ex
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  (S : StepLevel F E σ J T f bad)

def basePts : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) where
  carrier := {k | k ∈ levelAfL σ J S.Lb ∧ ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1}
  one_mem' := ⟨one_mem _, fun _ _ => map_one _⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun v h => by rw [map_mul, ha.2 v h, hb.2 v h, mul_one]⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, fun v h => by rw [map_inv, ha.2 v h, inv_one]⟩

theorem mem_basePts_iff (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : k ∈ basePts S ↔
    k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1 := by
  rw [← and_assoc, ← GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k]
  rfl

variable {S} (k : basePts S)

def basePtU : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨k.1, k.2.1.1⟩

theorem basePt_loc (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) k.1 ∈ levelVL σ J v S.Lb :=
  ((mem_basePts_iff S k.1).1 k.2).2.1 v

theorem conj_mem_iff {G : Type} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) (x : G) : a * x * a⁻¹ ∈ H ↔ x ∈ H := by
  rw [H.mul_mem_cancel_right (inv_mem ha), H.mul_mem_cancel_left ha]

def moveLev : StepLevel F E σ J T f bad :=
  { S with
    Uloc := fun v => (S.Uloc v).comap (MulAut.conj (bc (prV (E := E) v) k.1)).toMonoidHom
    Uloc_le := fun v x hx => (conj_mem_iff (H := UPts σ J (v.adicCompletion F)) (basePt_loc k v).1 x).1 (S.Uloc_le v hx)
    Uloc_lev := fun v x hx => (conj_mem_iff (basePt_loc k v) x).1 (S.Uloc_lev v hx)
    Uloc_hyp := fun v hv hT => by
      ext x
      rw [S.Uloc_hyp v hv hT]
      exact conj_mem_iff (basePt_loc k v) x
    UlocAlt := fun v h => by
      rw [← S.UlocAlt v h, k.2.2 v h]
      ext x
      simp
    U := S.U.comap (MulAut.conj k.1).toMonoidHom
    U_eq := fun x => by
      show k.1 * x * k.1⁻¹ ∈ S.U ↔ _
      rw [S.U_eq, conj_mem_iff (H := UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a := k.1) (basePtU k).2]
      refine and_congr_right fun _ => forall_congr' fun v => ?_
      rw [map_mul, map_mul, map_inv]
      rfl
    U_compact := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => k.1⁻¹ * x * k.1) :=
        (continuous_const.mul continuous_id).mul continuous_const
      convert S.U_compact.image hc using 1
      ext x
      constructor
      · intro hx
        exact ⟨k.1 * x * k.1⁻¹, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        show k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ ∈ S.U
        have e : k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ = y := by group
        rwa [e]
    U_open := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
        inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
      have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => basePtU k * x * (basePtU k)⁻¹) :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact S.U_open.preimage hc
    chi := S.chi.comp ((MulAut.conj k.1).toMonoidHom.subgroupComap S.U)
    chi_triv := fun x hx => S.chi_triv _ fun v hv => by
      show bc (prV (E := E) v) (k.1 * x.1 * k.1⁻¹) = 1
      rw [map_mul, map_mul, hx v hv, mul_one, ← map_mul, mul_inv_cancel, map_one] }

theorem mem_moveLev (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : x ∈ (moveLev k).U ↔ k.1 * x * k.1⁻¹ ∈ S.U := Iff.rfl

theorem moveLev_chi (x : (moveLev k).U) : (moveLev k).chi x = S.chi ⟨k.1 * x.1 * k.1⁻¹, x.2⟩ := rfl

def toMoved (κ : S.U) : (moveLev k).U :=
  ⟨k.1⁻¹ * κ.1 * k.1, by
    have e : k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1 := by group
    rw [mem_moveLev, e]
    exact κ.2⟩

theorem chi_toMoved (κ : S.U) : (moveLev k).chi (toMoved k κ) = S.chi κ := by
  rw [moveLev_chi]
  congr 1
  apply Subtype.ext
  show k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1
  group

theorem basePt_hatStab : HatStab S.Lb k.1 := fun z => ((inv_mem k.2.1).2 z).symm

theorem latAd_basePt [StarRing E] (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : latAd (x * k.1) S.Lb = latAd x S.Lb :=
  latAd_stab x k.1 S.Lb (basePt_hatStab k)

theorem cls_move_iff (x y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (x * basePtU k) : Cls (moveLev k)) = Quotient.mk'' (y * basePtU k) ↔
      (Quotient.mk'' x : Cls S) = Quotient.mk'' y := by
  refine (DoubleCoset.eq _ _ _ _).trans (Iff.trans ?_ (DoubleCoset.eq _ _ _ _).symm)
  refine exists_congr fun g => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨κ, hκ, e⟩
    refine ⟨basePtU k * κ * (basePtU k)⁻¹, hκ, ?_⟩
    rw [← mul_inv_cancel_right y (basePtU k), e]
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨(basePtU k)⁻¹ * κ * basePtU k, (toMoved k ⟨κ.1, hκ⟩).2, ?_⟩
    rw [e]
    group

theorem mem_hat_move_iff (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔
      ((y * k.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
        (moveLev k).Lb := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (inv_mem k.2.1).2 _

theorem map_conj_move (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (moveLev k).U.map (MulAut.conj (y * k.1)).toMonoidHom = S.U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (mem_moveLev k κ).1 hκ, Eq.trans ?_ e⟩
    show y * (k.1 * κ * k.1⁻¹) * y⁻¹ = y * k.1 * κ * (y * k.1)⁻¹
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (toMoved k ⟨κ, hκ⟩).2, Eq.trans ?_ e⟩
    show y * k.1 * (k.1⁻¹ * κ * k.1) * (y * k.1)⁻¹ = y * κ * y⁻¹
    group

theorem bij_move {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls S)) :
    Function.Bijective fun c => (Quotient.mk'' (y c * basePtU k) : Cls (moveLev k)) := by
  refine ⟨fun c c' e => h.1 ((cls_move_iff k _ _).1 e), fun q => ?_⟩
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨c, hc⟩ := h.2 (Quotient.mk'' (x * (basePtU k)⁻¹))
    refine ⟨c, ?_⟩
    have h := (cls_move_iff k _ _).2 hc
    rwa [inv_mul_cancel_right] at h

example : (moveLev (1 : basePts S)).U = S.U := by
  ext x
  simp [mem_moveLev]

example (κ : S.U) (h : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) : κ.1 ∈ basePts S :=
  (mem_basePts_iff S _).2 ⟨((S.U_eq _).1 κ.2).1, fun v => S.Uloc_lev v (((S.U_eq _).1 κ.2).2 v), h⟩

end Level

section Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}

set_option maxHeartbeats 1000000 in

def moveChart (K : LevelChart D T bad i hi stab lat) (k : basePts K.lev) : LevelChart D T bad i hi stab lat where
  lev := moveLev k
  y := fun c => K.y c * basePtU k
  y_bij := bij_move k K.y_bij
  y_lat := fun c x => (K.y_lat c x).trans (mem_hat_move_iff k (K.y c).1 x)
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := fun c γ => (K.stabI_range c γ).trans (SetLike.ext_iff.1 (map_conj_move k (K.y c).1) _).symm

end Chart

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

theorem norm_map_of_finOrder {K : Type} [Field K] (σ : K →+* ℂ) {ζ : Kˣ} (h : IsOfFinOrder ζ) : ‖σ (ζ : K)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one, norm_one]

theorem norm_muInvDet {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    (ht : Ch.Tied G.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j < R.m) {n : ℕ}
    (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) :
    ‖G.σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr)‖ = 1 := by
  have hU : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ), ‖(((G.mu0 ⟨j, hj⟩).locK P x : ℂˣ) : ℂ)‖ = 1 := fun P x =>
    (ht.mu0 ⟨j, hj⟩).unitary _
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      ‖G.σ₀ (Ch.muVal ⟨j, hj⟩ P : X.K)‖ = 1 := fun P hP => by
    rw [ht.muVal _ P hP]
    exact hU P (Formalism.L2.Host.unif P)
  have hfin := GlobalTheory.CharVal.finOrder_tup mu
  have h1 : ∀ P : rowSG Pr sel mu, ‖G.σ₀ (cst.muq (j + 1) P)‖ = 1 := by
    intro P
    have hq : ‖G.σ₀ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
      norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
    obtain ⟨hd, hn⟩ := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [hL.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl, norm_mul, norm_inv, hU, Units.val_inv_eq_inv_val, map_inv₀,
        norm_inv, hq]
      simp
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hL.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        norm_mul, norm_inv, norm_inv, hq, hval _ hg]
      simp
  have h2 : ‖G.σ₀ (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N)‖ = 1 := by
    unfold muOff
    refine finprod_induction (fun x => ‖G.σ₀ x‖ = 1) (by simp)
      (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · simp
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dif_pos hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul, norm_inv, norm_inv,
        hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX hPr hsel hv), norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
      simp
  rw [muInvDet, map_mul, norm_mul, h2, one_mul, map_prod, norm_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (j + 1) P) _
    ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2) (Units.ne_zero _)
  rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, h1, norm_map_of_finOrder _ hζ, one_zpow, one_mul]

def chiLat {D : D7} {X : Fields} (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) : ℂ :=
  χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N))

theorem norm_chiLat {D : D7} {X : Fields} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ} (hX : X.Ok) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) : ‖chiLat s χ n N‖ = 1 := by
  obtain ⟨-, t2, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  rw [chiLat, t6]
  generalize GlobalTheory.CharVal.detLat N = I at h1 h2
  obtain ⟨c1, h, y, hh, hy, hyI⟩ := GlobalTheory.NormOneIdeal.pow_eq_span_norm_one X.E I J h1 h2
  have hn : ∀ n : ℕ, TaylorLogMetric.N1 D (GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (I ^ n)) := fun n =>
    GlobalTheory.CharVal.normOne_idTo hs (c1 n) (by rw [← mul_pow, h2, one_pow])
  have hp : ∀ n : ℕ, χ (GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (I ^ n)) = χ (GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s I) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Submodule.one_eq_span, GlobalTheory.CharVal.chi_span hs hχ (by simp)]
      simp
    | succ n ih => rw [pow_succ, pow_succ, t2, hχ.1 _ _ (hn n) (GlobalTheory.CharVal.normOne_idTo hs h1 h2), ih]
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 ?_
  rw [← norm_pow, ← hp, ← hyI, GlobalTheory.CharVal.chi_span hs hχ hy, map_prod, norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have h4 := congrArg (s.σ₀.comp (X.emb τ)) hy
  rw [map_mul, hX.conjE, map_one] at h4
  have h5 := congrArg norm h4
  rw [norm_mul, Complex.norm_conj, norm_one, ← sq] at h5
  have h6 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5
  rw [RingHom.comp_apply] at h6
  rw [map_zpow₀, norm_zpow, h6, one_zpow]

end GlobalTheory.GO
end
end

