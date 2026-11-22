import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfIsUniUp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0153
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGenerat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.ShMem

theorem coeff_iterate_derivative' {R : Type} [CommRing R] (f : R⟦X⟧) (i n : ℕ) :
    coeff n ((PowerSeries.derivative R)^[i] f) = ((n + i).descFactorial i : R) * coeff (n + i) f := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative, ← add_assoc,
      Nat.succ_descFactorial_succ]
    push_cast; ring

theorem charZero_of_ql {l : ℕ} [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem coeff_sh {K : Type} [NormedField K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (e : ℕ) (f : K⟦X⟧) (i n : ℕ) :
    ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (sh f)) =
      (((n / e).factorial * (n + i).descFactorial i : ℕ) : K) * coeff (n + i) f := by
  have h := congrArg (coeff n) (hsh f i)
  rw [← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul, coeff_iterate_derivative'] at h
  push_cast
  rw [mul_comm (i.factorial : K), mul_assoc, h]; ring

theorem eventually_dvd {l : ℕ} [hl : Fact l.Prime] {e : ℕ} [NeZero e] (r : ℕ) :
    ∀ᶠ p : ℕ × ℕ in cofinite, l ^ r ∣ (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_lt_nat (l ^ r)).prod (Set.finite_lt_nat (e * l ^ r))).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq] at h
  refine ⟨?_, ?_⟩
  · show i < l ^ r
    by_contra hi; push_neg at hi
    exact h (Dvd.dvd.mul_left ((Nat.dvd_factorial (pow_pos hl.out.pos r) hi).trans
      (Nat.factorial_dvd_descFactorial _ _)) _)
  · show n < e * l ^ r
    by_contra hn; push_neg at hn
    apply h
    apply Dvd.dvd.mul_right
    apply Nat.dvd_factorial (pow_pos hl.out.pos r)
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne e))).2 (by rw [mul_comm]; exact hn)

theorem dvd_descFactorial {l n i : ℕ} (hi : i ≠ 0) (h : l ∣ n + i) : l ∣ (n + i).descFactorial i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [show n + j.succ = (n + j) + 1 from rfl, Nat.succ_descFactorial_succ]
  exact h.mul_right _

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

def nSh (e : ℕ) (p : ℕ × ℕ) : ℕ := (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1

variable (l a) in

def wSh (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  (nSh e p : Wq l a) * coeff (p.2 + p.1) (frobS l a x)

def wDiff (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  if p.1 ≠ 0 ∧ l ∣ nSh e p then ((nSh e p / l : ℕ) : Wq l a) * coeff (p.2 + p.1) (frobS l a x) else 0

theorem coeff_frobS_eq_zero (x : (Wq l a)⟦X⟧) {m : ℕ} (h : ¬ l ∣ m) : coeff m (frobS l a x) = 0 := by
  have : coeff m (frobS l a x) = if l ∣ m then sigma l a (coeff (m / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [this, if_neg h]

theorem tendsToZero_crystallinePrismShiftedFrobeniusCoeff {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wSh l a e x) := fun r =>
  (eventually_dvd (l := l) (e := e) r).mono fun p hp => by
    have h := Nat.cast_dvd_cast (α := Wq l a) hp
    rw [Nat.cast_pow] at h
    exact h.mul_right _

theorem tendsToZero_crystallinePrismShiftedCoeffDivPrime {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wDiff e x) := fun r =>
  (eventually_dvd (l := l) (e := e) (r + 1)).mono fun p hp => by
    unfold wDiff
    split_ifs with h
    · have h2 : l ^ r ∣ nSh e p / l := Nat.dvd_div_of_mul_dvd (by rw [← pow_succ']; exact hp)
      have h3 := Nat.cast_dvd_cast (α := Wq l a) h2
      rw [Nat.cast_pow] at h3
      exact h3.mul_right _
    · exact dvd_zero _

end Main

theorem shP_frob_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh x
  haveI : CharZero K := charZero_of_ql (l := l)
  have hkey : ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) *
      coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧))) = algebraMap O K (emb t τ (wSh l a e x (i, n))) := by
    intro τ i n
    rw [coeff_sh sh hsh e, coeff_toAc]
    simp only [wSh, nSh, map_mul, map_natCast, Nat.cast_mul]
  have hD : ∀ i n : ℕ, ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := fun i n =>
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  refine ⟨⟨wSh l a e x, tendsToZero_crystallinePrismShiftedFrobeniusCoeff x, fun τ i n => hkey τ i n⟩,
    fun τ => mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
      ((i.factorial * (n / e).factorial : ℕ) : K), ⟨wDiff e x, tendsToZero_crystallinePrismShiftedCoeffDivPrime x, fun τ i n => ?_⟩, ?_⟩
  · simp only [coeff_mk]; exact mul_div_cancel₀ _ (hD i n)
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    change coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧) - C (toAc t K (frobS l a x) τ : K⟦X⟧))) =
      coeff n (coeff i ((l : K⟦X⟧⟦X⟧) * mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
        ((i.factorial * (n / e).factorial : ℕ) : K)))
    rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul,
      coeff_mk, coeff_mk, map_sub, map_sub, coeff_C]
    by_cases hi : i = 0
    · subst hi
      have h0 : wDiff e x (0, n) = 0 := by simp [wDiff]
      rw [if_pos rfl, coeff_zero_eq_constantCoeff_apply, constantCoeff_sh sh hsh, sub_self, h0]
      simp
    · rw [if_neg hi, map_zero, sub_zero]
      apply mul_left_cancel₀ (hD i n)
      rw [hkey, mul_left_comm, mul_div_cancel₀ _ (hD i n)]
      unfold wDiff
      split_ifs with h
      · have h1 : (nSh e (i, n) : Wq l a) = l * ((nSh e (i, n) / l : ℕ) : Wq l a) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' h.2]
        simp only [wSh, h1, map_mul, map_natCast]
        ring
      · have hn : ¬ l ∣ n + i := fun hd => h ⟨hi, (dvd_descFactorial hi hd).mul_left _⟩
        simp [wSh, coeff_frobS_eq_zero x hn]

end GlobalTheory.CrysPrism.ShMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisValueFrobeniusOfInverseEisensteinTwis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PhiVal

theorem isCrisVal_phi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (hφ : D.phi y ∈ D.MMl), IsCrisVal t ϖ D.toPhiMod jB (phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩)) (jB (toBcris t ϖ D.toPhiMod ⟨D.phi y, hφ⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T jB y hY hy hφ
  have hEM : ∀ τ i, E K l e ^ η * y τ i ∈ A O K := fun τ i => mem_tot.1 ((Descent.mem_invOf _).1 hY).1 τ i
  let g : ι → ZMod a → A O K := fun i τ => ⟨E K l e ^ η * y τ i, hEM τ i⟩
  let m : OA l O := frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ η
  refine ⟨m, fun i => frobOA l O (ϖ.iTot t K (g i)), ?_, ?_, ?_⟩
  · rw [map_pow]
    exact (FrobEis.isUnit_toB_frob_eis l a e O ϖ).pow η
  · let EW : ZMod a → invE l e (A O K) := fun _ => ⟨(EIn l e (A O K) : K⟦X⟧), le_away _ _ (EIn l e (A O K)).2⟩
    have h2 : ϖ.iW t K EW = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) :=
      (ϖ.iW_of_mem t K (fun _ => EIn l e (A O K))).trans (congrArg _ (ϖ.iTot_E t K))
    have hA : ∀ i, inclO l O m * frobOW l O (toW t ϖ D.toPhiMod ⟨y, hy⟩ i) =
        inclO l O (frobOA l O (ϖ.iTot t K (g i))) := by
      intro i
      have h1 : ϖ.iW t K (fun τ => ⟨(g i τ : K⟦X⟧), le_away _ _ (g i τ).2⟩) =
          ϖ.iW t K EW ^ η * ϖ.iW t K (fun τ => ⟨y τ i, mem_tot.1 hy τ i⟩) := by
        rw [← map_pow, ← map_mul]
        congr 1
      rw [← frobOW_inclO, ← ϖ.iW_of_mem t K, h1, map_mul, h2, toW_apply, map_pow (inclO l O), map_pow (frobOW l O),
        frobOW_inclO]
    rw [phiW_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hA i]
  · rw [← LinearEquiv.map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, toBcris_apply]
    let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
      fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
    have key : liftA (frobAc l fun _ => EIn l e (A O K)) ^ η * coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i =
        liftA (frobAc l (g i)) := by
      funext τ
      apply Subtype.ext
      have h1 : (coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i τ : K⟦X⟧) = frob K l (y (τ - 1) i) := by
        change (D.mxInv τ *ᵥ D.phi y τ) i = _
        rw [PhiMod.phi_apply, Matrix.mulVec_mulVec, PhiMod.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
      simp only [liftA, Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, h1, coe_frobAc,
        frobTot_apply, g, map_mul, map_pow]
      rfl
    have h3 := congrArg (ϖ.iB t K) key
    simp only [map_mul, map_pow, liftA, FrobCoord.iB_of_A, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
    rw [← h3, map_pow]

end GlobalTheory.BKGal.PhiVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorLocalFieldIsCrystallineOverFamilyField
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocCrysU

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g), ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hFo i r hr Xs w hw n hP k M hSub hM
  obtain ⟨K', h, hN, hFi, hS, Sig, Fr, -, -, -, -, hx⟩ := hP
  obtain ⟨-, x₀, hx₀, j, hjinj, hjeq⟩ := hSub
  refine ⟨K', h, ?_⟩
  haveI := GlobalTheory.Pass.LocDirect.isTopRing i w hw
  have hcont := (GlobalTheory.Pass.FamCont.stepCont D i r hr x₀).1
  have hc1 : Continuous (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) :=
    GlobalTheory.PotDual.continuous_loc D i w hw _ hcont
  have hinc : Continuous (Subgroup.inclusion (GK_le h)) :=
    Continuous.subtype_mk continuous_subtype_val _

  have hpc := (hx ⟨x₀, hx₀⟩).1
  have hcr := ((GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hFi hS
    _ (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)))).2).1 hpc
  let A₁ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) hc1)
  let A₀ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM)

  let f := Br.toLLK (D.nbr i w hw)
  let J := (LinearMap.toMatrix' j).map f
  obtain ⟨jl, hjl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hjinj)
  have hJl : ((LinearMap.toMatrix' jl).map f) * J = 1 := by
    rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp, hjl, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero f) (map_one f)]
  let ι : A₀.V →ₗ[Br.LL D.nbr i w hw] A₁.V := Matrix.toLin' J
  have hinj : Function.Injective ι := by
    have e : ∀ z : Fin k → Br.LL D.nbr i w hw, ((LinearMap.toMatrix' jl).map f).mulVec (J.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec, hJl, Matrix.one_mulVec]
    intro u v huv
    have huv' : J.mulVec u = J.mulVec v := huv
    rw [← e u, ← e v, huv']
  have hJeq : ∀ γ : GE D.nd, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply, hjeq]
  have h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x) := by
    intro g (x : Fin k → Br.LL D.nbr i w hw)
    have hmat : J * Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g) =
        Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g) * J := by
      rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJeq]
    have key : J.mulVec ((Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g)).mulVec x) =
        (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g)).mulVec (J.mulVec x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
    exact key
  have hU : ∀ g, ∀ u ∈ LinearMap.range ι, A₁.ρ g u ∈ LinearMap.range ι := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A₀.ρ g x, h1 g x⟩
  let A₂ := A₁.quot (LinearMap.range ι) hU
  have hF := hFo (D.nd.l i) K' (D.nbr i w hw).LL
  exact ((hF.1 A₀ A₁ A₂ ι (LinearMap.range ι).mkQ h1 (fun _ _ => rfl) hinj (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm).1 hcr).1

end GlobalTheory.Pass.LocCrysU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZero
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.HubX.InvariantsNoJump

theorem mem_Jset_of_isJumpV (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (ha : IsJumpV S.PD Y.ρ τ a) : a ∈ LocalSituation.Jset S Y := by
  intro heq
  apply ha
  unfold FildR DdRE
  rw [inf_right_comm, heq, inf_right_comm]

theorem two_add_sum_jumps_le_intervalExponent (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (l m vd : ℕ)
    (hfin : (LocalSituation.Jset S Y).Finite) (h0 : ¬ IsJumpV S.PD Y.ρ τ 0) :
    2 + ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤ LocalSituation.cLL l m vd (LocalSituation.Jset S Y) 0 1 := by
  classical
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  unfold LocalSituation.cLL LocalSituation.rI
  rw [hI, Finset.sum_singleton]
  simp only [sub_zero]
  have hle : ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤
      ∑ᶠ (u : ℤ) (_ : u ∈ LocalSituation.Jset S Y) (_ : u ≠ 0), (m + LocalSituation.vZ l u) := by
    simp only [finsum_eq_if]
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    rotate_left
    all_goals try
      intro u hu
      rw [Set.Finite.coe_toFinset]
      by_contra hn
      have hn' : ¬ IsJumpV S.PD Y.ρ τ u := fun hj => hn (mem_Jset_of_isJumpV S Y τ u hj)
      apply hu
      simp [hn, hn']
    apply Finset.sum_le_sum
    · intro u _
      by_cases hj : IsJumpV S.PD Y.ρ τ u
      · have hu0 : u ≠ 0 := by rintro rfl; exact h0 hj
        simp only [if_pos hj, if_pos (mem_Jset_of_isJumpV S Y τ u hj), if_pos hu0, le_refl]
      · simp only [if_neg hj]
        exact Nat.zero_le _
  omega

end GlobalTheory.HubX.InvariantsNoJump

namespace GlobalTheory.HubX.InvariantsNoJump

theorem torsion_exponent_kills_invariants_no_jump_zero : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  intro _ _ _ D HW F _ l _ K s LL h S M0 h0 T hW hJ x hx
  have hat := GlobalTheory.T.invariants_vanish_at_prime_of_admissible D HW F (GlobalTheory.Per.FontaineAll.fontaine_bounds D) l K s LL h
  have hp : LocalSituation.ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hcard := Formalism.MainNotions.N.JsetEmb.card_emb_good h
  have hpos : 0 < Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    rw [hcard]; exact Module.finrank_pos
  obtain ⟨τ⟩ := (Nat.card_pos_iff.1 hpos).1
  have key := hat M0 h0 T τ hW (hJ τ) x hx
  have hfin : (LocalSituation.Jset S T).Finite :=
    (Set.finite_Icc (-(M0 : ℤ)) h0).subset fun a ha => hW.2.1 a ha
  have hle : LocalSituation.c0 S T τ M0 h0 ≤ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T := by
    unfold LocalSituation.c0
    rw [hp, hs]
    exact two_add_sum_jumps_le_intervalExponent S T τ l _ _ hfin (hJ τ)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm, mul_smul, key, smul_zero]

end GlobalTheory.HubX.InvariantsNoJump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSum
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ExactMult

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, wh ψ (f i) := by
  unfold wh tr
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun h => c * f h) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem wh_gg_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (gg ψ 0) = 1 := by
  have hU : ∀ M : Mt g 0, IsUniUp M := fun M a => a.elim0
  have hgg : ∀ x : Gn g 0, gg ψ 0 x = 1 := by
    intro x
    unfold gg
    simp [hU]
  unfold wh eU
  rw [GlobalTheory.GLm.TraceTail.tr_eDat]
  simp [hU, hgg]

theorem isClass_der (ψ : AddChar (ZMod g) ℂ) {N : ℕ} (i : ℕ) (hi : i ≤ N) (χ : Gn g N → ℂ)
    (hχ : IsClass χ) : IsClass (der ψ i χ) := by
  intro x y
  have h := ((GlobalTheory.GLq.HcClass.hc_class g i (N - i) N (by omega)).2 χ hχ).2
  unfold der
  congr 1
  funext z
  exact h z x y

theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ)
    (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β (a + b)) = wh ψ α * wh ψ β := by
  unfold hc
  rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ a b (a + b) rfl _ (fun y x z => by simp only [hα x z])
    (fun x y z => by simp only [hβ y z])]
  simp only [wh_const_mul]
  rw [show (fun x => α x * wh ψ β) = (fun x => wh ψ β * α x) from funext fun _ => mul_comm _ _,
    wh_const_mul, mul_comm]

end GlobalTheory.GLq.ExactMult

namespace GlobalTheory.GLq.ExactMult

open GlobalTheory.GLm

theorem tr_eJ'_eq_sum_wh_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k : ℕ), 1 ≤ k →
    k < N → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ' g N k ψ) χ =
      (∑ i ∈ Finset.range k, wh ψ (der ψ i χ) * ((g : ℂ) ^ (k - i) - (g : ℂ) ^ (k - i - 1))) +
        wh ψ (der ψ k χ) := by
  intro g _ ψ hψ N k _ hk χ hχ
  rw [tr_eJ'_eq_wh_tail g ψ N k χ hk]
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have hF := GlobalTheory.GLm.TailClass.isMirClass_tail g ψ (k + 1) N χ (by omega) (by omega) hM
  rw [show (fun h => tail ψ (k + 1) χ (diag1 h (k + 1))) = fun h =>
      ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k h from
    funext (mirClass_diag1_eq_sum g ψ hψ k _ hF)]
  rw [wh_sum, Finset.sum_range_succ]
  have key : ∀ i, i < k + 1 → wh ψ (hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k) =
      wh ψ (der ψ i χ) * wh ψ (gg ψ (k - i)) := by
    intro i hi
    rw [GlobalTheory.GLm.DerTail.der_tail g ψ i (k + 1) N χ hi (by omega)]
    have := wh_hc ψ hψ i (k - i) (der ψ i χ) (gg ψ (k - i)) (isClass_der ψ i (by omega) χ hχ)
      (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ (k - i)).2
    rwa [show i + (k - i) = k by omega] at this
  rw [key k (by omega), Nat.sub_self, wh_gg_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [key i (by omega), (GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity g ψ hψ (k - i) (by omega)).1]

end GlobalTheory.GLq.ExactMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGe
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem pow_dvd_factorial_mul (l r : ℕ) (hl : 1 ≤ l) : l ^ r ∣ (l * r).factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : l * (r + 1) = (l * (r + 1) - 1) + 1 := by
      have : 1 ≤ l * (r + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [h1, Nat.factorial_succ, ← h1, pow_succ, mul_comm (l ^ r) l]
    refine Nat.mul_dvd_mul (Dvd.intro (r + 1) rfl) (ih.trans (Nat.factorial_dvd_factorial ?_))
    rw [Nat.mul_succ]; omega

theorem inclS_mem_SdSet (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (x : (Wq l a)⟦X⟧) :
    inclS t K x ∈ SdSet t K e := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  refine ⟨fun n => ((n / e).factorial : Wq l a) * coeff n x, fun r => ?_, fun τ n => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat (e * (l * r))).subset fun n hn => ?_
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hlt
    apply hn
    have hle : l * r ≤ n / e := (Nat.le_div_iff_mul_le he).2 (by rw [mul_comm]; omega)
    obtain ⟨k, hk⟩ := (pow_dvd_factorial_mul l r hl1).trans (Nat.factorial_dvd_factorial hle)
    refine Dvd.dvd.mul_right ⟨(k : Wq l a), ?_⟩ _
    rw [hk]; push_cast; rfl
  · rw [inclS_apply, coeff_toAc, map_mul, map_natCast, map_mul, map_natCast]

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPowStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.NL.PhiSpanKer.main | exact GlobalTheory.NL.PhiSpanKer.main | (intros; apply GlobalTheory.NL.PhiSpanKer.main <;> assumption)
end

