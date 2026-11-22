import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWachModuleMapMatrixReductionComm
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachMap

section Gen

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M} {n : ℕ}

theorem coeff_unique (b : Module.Basis (Fin n) R S) {c d : Fin n → R}
    (h : ∑ j, c j • (b j : M) = ∑ j, d j • (b j : M)) : c = d := by
  have h' : ∑ j, c j • b j = ∑ j, d j • b j := Subtype.ext (by simpa using h)
  exact (b.repr_sum_self c).symm.trans ((congrArg (fun y => ⇑(b.repr y)) h').trans (b.repr_sum_self d))

theorem exists_coeff (b : Module.Basis (Fin n) R S) {x : M} (hx : x ∈ S) :
    ∃ c : Fin n → R, x = ∑ j, c j • (b j : M) := by
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at e
  exact e.symm

theorem sum_smul_sum {m : ℕ} (a : Fin m → R) (B : Fin m → Fin n → R) (e : Fin n → M) :
    ∑ k, a k • ∑ j, B k j • e j = ∑ j, (∑ k, a k * B k j) • e j := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end Gen

def incHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] : O⟦X⟧ →+* O⟦X⟧ where
  toFun := inc l O
  map_one' := by simpa using (pi0Subst_laws_hold l O).2.2.1 1
  map_mul' := (pi0Subst_laws_hold l O).2.1
  map_zero' := by simpa using (pi0Subst_laws_hold l O).2.2.1 0
  map_add' := (pi0Subst_laws_hold l O).1

theorem incHom_apply (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (y : O⟦X⟧) :
    incHom l O y = inc l O y := rfl

theorem map_one_add_X_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (D : Mx R⟦X⟧ m m) :
    (1 + (X : R⟦X⟧) • D).map (PowerSeries.map f) = 1 + (X : S⟦X⟧) • D.map (PowerSeries.map f) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

end GlobalTheory.WachMap

namespace GlobalTheory.WachMap

theorem coeff_comm {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {S' : Submodule R M'} {n n' : ℕ} (e : Fin n → M) (b' : Module.Basis (Fin n') R S')
    (g : M →+ M') (u : M →+ M) (u' : M' →+ M') (σ : R → R) (hg : ∀ (a : R) x, g (a • x) = a • g x)
    (hu' : ∀ (a : R) x, u' (a • x) = σ a • u' x) (hc : ∀ x, g (u x) = u' (g x))
    (p : Fin n → Fin n → R) (p' : Fin n' → Fin n' → R) (A : Fin n' → Fin n → R)
    (hp : ∀ k, u (e k) = ∑ m, p m k • e m) (hp' : ∀ k, u' (b' k : M') = ∑ m, p' m k • (b' m : M'))
    (hA : ∀ k, g (e k) = ∑ m, A m k • (b' m : M')) (j : Fin n') (k : Fin n) :
    ∑ m, p m k * A j m = ∑ m, σ (A m k) * p' j m := by
  have h1 : g (u (e k)) = ∑ j, (∑ m, p m k * A j m) • (b' j : M') := by
    rw [hp k, map_sum]
    simp only [hg, hA]
    exact sum_smul_sum (fun m => p m k) (fun m j => A j m) (fun j => (b' j : M'))
  have h2 : u' (g (e k)) = ∑ j, (∑ m, σ (A m k) * p' j m) • (b' j : M') := by
    rw [hA k, map_sum]
    simp only [hu', hp']
    exact sum_smul_sum (fun m => σ (A m k)) (fun m j => p' j m) (fun j => (b' j : M'))
  have hc' := coeff_unique (c := fun j => ∑ m, p m k * A j m) (d := fun j => ∑ m, σ (A m k) * p' j m) b'
    ((h1.symm.trans (hc (e k))).trans h2)
  exact congrFun hc' j

theorem mul_eq_of_inc {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (hl : l ≠ 2) {n n' : ℕ}
    (P : Mx O⟦X⟧ n n) (P' : Mx O⟦X⟧ n' n') (A A' : Mx O⟦X⟧ n' n)
    (h : ∀ j k, ∑ m, inc l O (P m k) * inc l O (A j m) = ∑ m, inc l O (A' m k) * inc l O (P' j m)) :
    P' * A' = A * P := by
  refine Matrix.ext fun j k => ?_
  apply (pi0Subst_laws_hold l O).2.2.2.2.2.2.2 hl
  simp only [Matrix.mul_apply]
  show incHom l O (∑ m, P' j m * A' m k) = incHom l O (∑ m, A j m * P m k)
  simp only [map_sum, map_mul, incHom_apply]
  rw [Finset.sum_congr rfl fun m _ => mul_comm (inc l O (P' j m)) (inc l O (A' m k)), ← h j k]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {L O : Type} [Field L] [Algebra Qp L]
    [CommRing O] [Algebra O L] [TopologicalSpace L] {v : AddValuation L (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD L O v f)

theorem phiD_smul (T : LocLat G Qp L O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = letφ W.φ₀ a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

theorem gamD_smul (T : LocLat G Qp L O) (γ : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T γ (a • x) = letγ (W.γ₀ γ) a • W.γD T γ x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem map_smul_letA {T T' : LocLat G Qp L O} (g : LatHom T.L T'.L) (a : LetA O f)
    (x : W.DD T) : W.map g (a • x) = a • W.map g x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {T T' : LocLat G Qp L O} {n n' : ℕ}
  (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
  {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_mapMat (RF : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (g : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hb' : ∀ k, (b' k : W.DD T') ∈ W.NΔ T') :
    ∃ A : ZMod f → Mx O⟦X⟧ n' n, ∀ k, W.map g (b k : W.DD T) =
      ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T') := by
  classical
  have key : ∀ k, ∃ c : Fin n' → LetA O f, W.map g (b k : W.DD T) = ∑ m, c m • (b' m : W.DD T') ∧
      ∀ m i, ∀ δ ∈ W.DelF, W.γ₀ δ (c m i) = c m i := by
    intro k
    have hk : (b k : W.DD T) ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b k : W.DD T) = b k := hb k
    have hy : W.map g (b k : W.DD T) ∈ W.N T' := W.map_N g hT hT' _ hk.1
    obtain ⟨c, hc⟩ := exists_coeff b' hy
    refine ⟨c, hc, fun m i δ hδ => ?_⟩
    have hb2 : ∀ m, W.γD T' δ (b' m : W.DD T') = b' m := fun m =>
      (show (b' m : W.DD T') ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ (b' m : W.DD T') = b' m from hb' m).2 δ hδ
    have e1 : W.γD T' δ (W.map g (b k : W.DD T)) = W.map g (b k : W.DD T) := by
      rw [← W.map_γ, hk.2 δ hδ]
    rw [hc, map_sum] at e1
    simp only [gamD_smul, hb2] at e1
    have e2 := coeff_unique (c := fun m => letγ (W.γ₀ δ) (c m)) (d := c) b' e1
    exact congrFun (congrFun e2 m) i
  choose c hc hinv using key
  refine ⟨fun i m k => Classical.choose (RF (c k m i) (fun δ hδ => hinv k m i δ hδ)), fun k => ?_⟩
  rw [hc k]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  funext i
  exact (Classical.choose_spec (RF (c k m i) (fun δ hδ => hinv k m i δ hδ))).symm

variable {F : Type} [Field F] [Algebra ℤ_[l] F] [CharP F l] (red : O →+* F)

theorem red_frob (hl : l ≠ 2) (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] F z)
    (hφ : ∀ a, W.φ₀ a = phi l O a) (g : LatHom T.L T'.L) (P : ZMod f → Mx O⟦X⟧ n n) (P' : ZMod f → Mx O⟦X⟧ n' n')
    (A : ZMod f → Mx O⟦X⟧ n' n)
    (hP : ∀ k, W.φD T (b k : W.DD T) = ∑ m, (fun i => inc l O (P i m k) : LetA O f) • (b m : W.DD T))
    (hP' : ∀ k, W.φD T' (b' k : W.DD T') = ∑ m, (fun i => inc l O (P' i m k) : LetA O f) • (b' m : W.DD T'))
    (hA : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (i : ZMod f) :
    (P' i).map (PowerSeries.map red) * ((A (i - 1)).map (PowerSeries.map red)).map (frob0 l) =
      (A i).map (PowerSeries.map red) * (P i).map (PowerSeries.map red) := by
  classical
  have hc := fun j k => coeff_comm (fun k => (b k : W.DD T)) b'
    (W.map g).toAddMonoidHom (W.φD T).toAddMonoidHom (W.φD T').toAddMonoidHom (letφ W.φ₀)
    (fun a x => map_smul_letA W g a x) (fun a x => phiD_smul W T' a x) (fun x => W.map_φ g x)
    (fun m k => (fun i => inc l O (P i m k) : LetA O f)) (fun m k => (fun i => inc l O (P' i m k) : LetA O f))
    (fun m k => (fun i => inc l O (A i m k) : LetA O f)) hP hP' hA j k
  have hred' : ∀ y : O⟦X⟧, (∃ y', phi l O (inc l O y) = inc l O y') ∧
      ∀ y', phi l O (inc l O y) = inc l O y' → PowerSeries.map red y' = frob0 l (PowerSeries.map red y) :=
    frobenius_on_pi0Subst_holds l O F red hl hred
  let Y : Mx O⟦X⟧ n' n := fun m k => Classical.choose (hred' (A (i - 1) m k)).1
  have hY : ∀ m k, phi l O (inc l O (A (i - 1) m k)) = inc l O (Y m k) := fun m k =>
    Classical.choose_spec (hred' (A (i - 1) m k)).1
  have hi : ∀ j k, ∑ m, inc l O (P i m k) * inc l O (A i j m) = ∑ m, inc l O (Y m k) * inc l O (P' i j m) := by
    intro j k
    have e := congrFun (hc j k) i
    rw [Finset.sum_apply, Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun m _ => ?_)
    show W.φ₀ (inc l O (A (i - 1) m k)) * inc l O (P' i j m) = _
    rw [hφ, hY m k]
  have hM : P' i * Y = A i * P i := mul_eq_of_inc hl (P i) (P' i) (A i) Y hi
  have hYr : Y.map (PowerSeries.map red) = ((A (i - 1)).map (PowerSeries.map red)).map (frob0 l) := by
    refine Matrix.ext fun m k => ?_
    exact (hred' (A (i - 1) m k)).2 _ (hY m k)
  rw [← hYr, ← Matrix.map_mul, hM, Matrix.map_mul]

omit [Algebra ℤ_[l] F] in

theorem red_gam (hl : l ≠ 2) (γ : W.Gam) (u : ℤ_[l]) (un : O⟦X⟧) (hun : IsUn l O u un)
    (hγ : ∀ a, W.γ₀ γ a = act l O u a) (g : LatHom T.L T'.L) (D : ZMod f → Mx O⟦X⟧ n n)
    (D' : ZMod f → Mx O⟦X⟧ n' n') (A : ZMod f → Mx O⟦X⟧ n' n)
    (hD : ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • D i) m k) : LetA O f) • (b m : W.DD T))
    (hD' : ∀ k, W.γD T' γ (b' k : W.DD T') =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • D' i) m k) : LetA O f) • (b' m : W.DD T'))
    (hA : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (i : ZMod f) :
    (1 + (X : F⟦X⟧) • (D' i).map (PowerSeries.map red)) *
        ((A i).map (PowerSeries.map red)).map (gam0 0 (PowerSeries.map red un)) =
      (A i).map (PowerSeries.map red) * (1 + (X : F⟦X⟧) • (D i).map (PowerSeries.map red)) := by
  classical
  have hc := fun j k => coeff_comm (fun k => (b k : W.DD T)) b'
    (W.map g).toAddMonoidHom (W.γD T γ).toAddMonoidHom (W.γD T' γ).toAddMonoidHom (letγ (W.γ₀ γ))
    (fun a x => map_smul_letA W g a x) (fun a x => gamD_smul W T' γ a x) (fun x => W.map_γ g γ x)
    (fun m k => (fun i => inc l O ((1 + (X : O⟦X⟧) • D i) m k) : LetA O f))
    (fun m k => (fun i => inc l O ((1 + (X : O⟦X⟧) • D' i) m k) : LetA O f))
    (fun m k => (fun i => inc l O (A i m k) : LetA O f)) hD hD' hA j k
  have hi : ∀ j k, ∑ m, inc l O ((1 + (X : O⟦X⟧) • D i) m k) * inc l O (A i j m) =
      ∑ m, inc l O ((A i).map (gam0 (l : O) un) m k) * inc l O ((1 + (X : O⟦X⟧) • D' i) j m) := by
    intro j k
    have e := congrFun (hc j k) i
    rw [Finset.sum_apply, Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun m _ => ?_)
    show W.γ₀ γ (inc l O (A i m k)) * inc l O ((1 + (X : O⟦X⟧) • D' i) j m) = _
    rw [hγ, gamma_on_pi0Subst_holds l O u un hun]
    rfl
  have hM := mul_eq_of_inc hl (1 + (X : O⟦X⟧) • D i) (1 + (X : O⟦X⟧) • D' i) (A i) ((A i).map (gam0 (l : O) un)) hi
  have hG : ((A i).map (gam0 (l : O) un)).map (PowerSeries.map red) =
      ((A i).map (PowerSeries.map red)).map (gam0 0 (PowerSeries.map red un)) := by
    refine Matrix.ext fun m k => ?_
    simp only [Matrix.map_apply]
    rw [gamma_reduction_holds O F red (l : O) un (A i m k), map_natCast, CharP.cast_eq_zero]
  rw [← hG, ← map_one_add_X_smul red (D' i), ← map_one_add_X_smul red (D i), ← Matrix.map_mul, hM, Matrix.map_mul]

end Local

theorem charP_residueField_of_irreducible {l : ℕ} [Fact l.Prime] (LL : FinExt l) : CharP (ResidueField ↥(OL LL)) l := by
  have hl : l.Prime := Fact.out
  have : Algebra.IsIntegral ℤ_[l] ↥(OL LL) := ⟨fun x => integralClosure.isIntegral x⟩
  rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue ↥(OL LL)), IsLocalRing.residue_eq_zero_iff]
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal ↥(OL LL))
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hmem : (l : ℤ_[l]) ∈ (IsLocalRing.maximalIdeal ↥(OL LL)).comap (algebraMap ℤ_[l] ↥(OL LL)) := by
    rw [heq, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using hmem

set_option maxHeartbeats 1000000 in

theorem exists_mapMat_redHom : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  intro l _ P H K LL hA T T' n n' γ b b' N N' u un g hT hT' hF hF' hχ hun
  have hl : l ≠ 2 := hA.2.1
  have := charP_residueField_of_irreducible LL
  obtain ⟨hφ, -, hγ, -, hRF, -⟩ := GlobalTheory.T.wachRingFacts_unramified_levelOne H K LL hA
  have RF : ∀ a : (↥(OL LL))⟦X⟧, (∀ δ ∈ (H.W K 1 LL hA.2.2).DelF, (H.W K 1 LL hA.2.2).γ₀ δ a = a) →
      ∃ y, inc l ↥(OL LL) y = a := fun a ha => (hRF a).mp ha
  obtain ⟨A, hAm⟩ := exists_mapMat (H.W K 1 LL hA.2.2) b b' RF g hT hT' hF.1 hF'.1
  refine ⟨A, hAm, fun i => ⟨?_, ?_⟩⟩
  · exact red_frob (H.W K 1 LL hA.2.2) b b' (residue ↥(OL LL)) hl (fun z => rfl) hφ g N.P N'.P A
      hF.2.1 hF'.2.1 hAm i
  · exact red_gam (H.W K 1 LL hA.2.2) b b' (residue ↥(OL LL)) hl γ u un hun (hγ γ u hχ) g N.D N'.D A
      hF.2.2.1 hF'.2.2.1 hAm i

end GlobalTheory.WachMap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParameters
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MonoVal

theorem isQuasiRegularSeq_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q),
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 →
    IsNoetherianRing Q ∧ IsQuasiRegularSeq Q z := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z hm hd
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  refine ⟨inferInstance, isQuasiRegularSeq_of_isRegular ?_⟩
  refine isRegular_of_ofList_eq_maximalIdeal ?_ ?_
  · rw [ofList_ofFn_eq_span_range, hm]
  · rw [List.length_ofFn, hd]
    norm_cast

def powCoeffMatrix {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ) (w : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (if j = 0 then 1 else 0)
    (fun i' => Fin.cases (w i' * ((e i' : A) * t ^ (e i' - 1)))
      (fun j' => if j' = i' then t ^ e i' else 0) j) i

theorem powCoeffMatrix_det {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ)
    (w : Fin n → A) : (powCoeffMatrix n t e w).det = t ^ (∑ i, e i) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [powCoeffMatrix, Finset.prod_pow_eq_pow_sum]
  · intro i j hij
    change i < j at hij
    induction i using Fin.cases with
    | zero =>
      have : j ≠ 0 := (Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) hij))
      simp [powCoeffMatrix, this]
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j' =>
        have : j' ≠ i' := by
          intro h; subst h; exact lt_irrefl _ hij
        simp [powCoeffMatrix, this]

theorem dForm_cons_pow_mul : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (n : ℕ) (t : A)
    (e : Fin n → ℕ) (w : Fin n → A),
    dForm α (Fin.cons t (fun i => t ^ e i * w i) : Fin (n + 1) → A) =
      t ^ (∑ i, e i) • dForm α (Fin.cons t w : Fin (n + 1) → A) := by
  intro k A _ _ α n t e w
  rw [← powCoeffMatrix_det n t e w]
  apply dForm_eq_det_smul
  intro i
  rw [Fin.sum_univ_succ]
  induction i using Fin.cases with
  | zero => simp [powCoeffMatrix]
  | succ i' =>
    simp only [powCoeffMatrix, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    letI := α.toAlgebra
    change KaehlerDifferential.D k A (t ^ e i' * w i') = _
    rw [Derivation.leibniz, Derivation.leibniz_pow, add_comm]
    congr 1
    rw [mul_smul, mul_smul, ← Nat.cast_smul_eq_nsmul A]

theorem monomial_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r N z wt hm hdim hw0 hw1 hx
  obtain ⟨hN, hqr⟩ := isQuasiRegularSeq_of_locModel c Q hQ r z hm hdim
  obtain ⟨V, hC, u, hu, hirr, hmV, hunit, hloc⟩ := GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel c Q hQ r z wt hN hm.symm hqr hw0 hw1
  have ht0 : (z 0 : L) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hordt : V.ord (z 0 : L) = 1 := by
    have h := V.ord_irreducible hirr
    exact h
  have h1m : (1 : Q) ∉ IsLocalRing.maximalIdeal Q := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have huu : ∀ i, IsUnit (u i) := fun i => by
    have h := hunit (MvPolynomial.X i) ⟨Finsupp.single i 1, by rw [MvPolynomial.coeff_X, if_pos rfl]; exact h1m⟩
    rw [MvPolynomial.eval₂_X] at h
    exact h
  have hu0 : ∀ i, (u i : L) ≠ 0 := fun i h => (huu i).ne_zero (Subtype.ext h)
  have hordu : ∀ i, V.ord (u i : L) = 0 := fun i => V.ord_eq_zero (huu i)
  have hordz : ∀ i, V.ord (z i : L) = wt i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hordt, hw0]; rfl
    · rw [← hu i, V.ord_mul (hu0 i) (pow_ne_zero _ ht0), V.ord_pow, hordu i, hordt]
      simp

  obtain ⟨φ, hφ⟩ : ∃ φ : Q →+* V.ring, φ = Q.subtype.codRestrict V.ring fun q => hC _ q.2 :=
    ⟨_, rfl⟩
  have hφL : ∀ q : Q, ((φ q : V.ring) : L) = q := fun q => by rw [hφ]; rfl
  refine ⟨V, hC, fun q hq => ?_, hordz, ?_, ?_⟩
  · have h := V.ord_eq_zero (hq.map φ)
    rwa [hφL] at h
  · intro d q hq0 hq
    have hmap : Ideal.map φ (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring)} := by
      rw [← hirr.maximalIdeal_eq, Ideal.map_le_iff_le_comap]
      intro q hq
      have h := hmV q hq
      rw [Ideal.mem_comap]
      convert h using 1
      exact Subtype.ext (hφL q)
    have h2 : φ q ∈ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring) ^ d} := by
      rw [← Ideal.span_singleton_pow]
      refine (Ideal.pow_right_mono hmap d) ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem φ hq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
    have haL : (q : L) = (a : L) * (z 0 : L) ^ d := by
      rw [← hφL q, ← ha]
      rfl
    have ha0 : (a : L) ≠ 0 := fun h => hq0 (by rw [haL, h, zero_mul])
    rw [haL, V.ord_mul ha0 (pow_ne_zero _ ht0), V.ord_pow, hordt, mul_one]
    have := (V.ord_nonneg_iff ha0).2 a.2
    omega

  · intro y hy
    obtain ⟨xT, hxT⟩ := hx
    obtain ⟨j, s, hjN, hsu⟩ := GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place c Q hQ N r V hC u ⟨xT, hxT⟩ hmV hunit hloc
    subst hjN
    obtain ⟨w, hw⟩ : ∃ w : Fin (r + j) → V.ring,
        w = Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring) := ⟨_, rfl⟩
    rw [← hw] at hsu
    have hG : IsFreeGen V.ring
        (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      letI := V.const.toAlgebra
      letI := c.toAlgebra
      haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
      haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
      haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
      obtain ⟨m, z', b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ hirr
      have h1 := trdeg_eq_of_basis_kaehler ℂ L b
      have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hxT
      rw [h1, Cardinal.mk_fin] at h2
      obtain rfl : r + j = m := by
        have : r + j + 1 = m + 1 := by exact_mod_cast h2
        omega
      exact isFreeGen_dForm_uniformiser_cons ℂ V.ring V.const (r + j) _ w V.essFiniteType hirr
        ⟨b⟩ hsu
    have e1 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) =
        V.toRat (r + j + 1)
          (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      have h := TopForm.formMap_dForm (D := r + j + 1) (α := V.const) (β := c) V.ring.subtype rfl
        (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)
      refine Eq.trans ?_ h.symm
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    have hθ0 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) ≠ 0 := by
      rw [e1]; exact V.toRat_ne_zero hG
    have hθ : V.formOrd
        (dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L)) = 0 := by
      rw [e1]; exact V.formOrd_toRat hG
    obtain ⟨a, ha⟩ := hy.2 (dForm (c.codRestrict Q hQ.const_mem)
      (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q))
    have e2 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) = (a : L) • dForm c (fun i => (y i : L)) := by
      have h := congrArg (TopForm.formMap (r + j + 1) Q.subtype
        (α := c.codRestrict Q hQ.const_mem) (β := c) rfl) ha
      have f1 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl y
      have f2 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q)
      rw [map_smulₛₗ] at h
      exact f2.symm.trans (h.symm.trans (congrArg (Q.subtype a • ·) f1))
    obtain ⟨e, he⟩ : ∃ e : Fin (r + j) → ℕ,
        e = Fin.append (fun i => wt i.succ) (fun _ : Fin j => 0) := ⟨_, rfl⟩
    have e3 : (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (Fin.cons (z 0 : L) (fun i => (z 0 : L) ^ e i * (w i : L)) : Fin (r + j + 1) → L) := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      simp only [Fin.cons_succ]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [he, hw, Fin.append_left]
        rw [← hu i, mul_comm]
      · simp only [he, hw, Fin.append_right, pow_zero, one_mul]
    have hsum : ∑ i, e i = ∑ i : Fin r, wt i.succ := by
      rw [he, Fin.sum_univ_add]
      simp
    have e4 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (z 0 : L) ^ (∑ i : Fin r, wt i.succ) •
          dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) := by
      rw [e3, dForm_cons_pow_mul, hsum]
    have hpow0 : ((z 0 : L) ^ (∑ i : Fin r, wt i.succ)) ≠ 0 := pow_ne_zero _ ht0
    have hne : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) ≠ 0 := by
      rw [e4]
      exact smul_ne_zero hpow0 hθ0
    have ha0 : (a : L) ≠ 0 := fun h => hne (by rw [e2, h, zero_smul])
    have hy0 : dForm c (fun i => (y i : L)) ≠ 0 := fun h => hne (by rw [e2, h, smul_zero])
    have o1 := V.formOrd_smul hxT hθ0 hpow0
    have o2 := V.formOrd_smul hxT hy0 ha0
    rw [← e4, hθ, V.ord_pow, hordt] at o1
    rw [← e2, o1] at o2
    have hnna := (V.ord_nonneg_iff ha0).2 (hC _ a.2)
    rw [Fin.sum_univ_succ, hw0]
    push_cast at o2 ⊢
    linarith

end GlobalTheory.MonoVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilatedStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremal_vector_annihilated : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ v : M.Vec, IsExtVec M v → ∀ (ρ : D.what₂.Tau) (p : ℕ) (s : Bool), (∀ a : Fin V.rank, M.ε ρ a = if (a : ℕ) < p then s else !s) → (∀ a b, KillPair (M.ε ρ) a b → RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧ ∀ (t : Fin V.rank → ℝ) (g : GA D V), T v (g * atTau θ V ρ ((M.fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I)) * M.fr ρ)) = Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) * T v g := by
  first | exact @GlobalTheory.HolRead.ExtKill.kill_and_weight | exact GlobalTheory.HolRead.ExtKill.kill_and_weight | (intros; apply GlobalTheory.HolRead.ExtKill.kill_and_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ x y : finU E n, (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  first | exact @GlobalTheory.BCT.finU_eq_of_loc | exact GlobalTheory.BCT.finU_eq_of_loc | (intros; apply GlobalTheory.BCT.finU_eq_of_loc <;> assumption)
end

