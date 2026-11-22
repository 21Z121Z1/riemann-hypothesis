import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0581
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinks
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.DRLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

private theorem hom_frobenius_pt {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
    (f : WittVector p R →+* WittVector p R) (x : WittVector p R) :
    f (WittVector.frobenius x) = WittVector.frobenius (f x) := by
  have h1 : ∀ z : WittVector p R, (p : WittVector p R) ∣ WittVector.frobenius z - z ^ p := by
    intro z
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : WittVector.constantCoeff (WittVector.frobenius z - z ^ p) = 0 := by
      rw [map_sub, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, sub_self]
    exact this
  have h2 : ∀ y : R, WittVector.frobenius (WittVector.teichmuller p y) = WittVector.teichmuller p y ^ p := by
    intro y
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have h3 : ∀ n : ℕ, f (WittVector.frobenius x) - WittVector.frobenius (f x) ∈
      Ideal.span {(p : WittVector p R) ^ n} := by
    intro n
    have hnil : IsNilpotent ((p : ℕ) : WittVector p R ⧸ Ideal.span {(p : WittVector p R) ^ n}) := by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have := WittVector.eq_of_apply_teichmuller_eq
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (f.comp WittVector.frobenius))
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (WittVector.frobenius.comp f)) hnil (by
        intro y
        obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv R p n).surjective y
        simp only [RingHom.comp_apply]
        rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton, h2, iterateFrobeniusEquiv_def]
        simp only [map_pow]
        rw [pow_right_comm]
        exact (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub (h1 _) n))
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun this x)
  rw [← sub_eq_zero]
  refine WittVector.ext fun n => ?_
  rw [WittVector.zero_coeff]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).1 (h3 _) n (Nat.lt_succ_self n)

theorem σA_frob (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) :=
  hom_frobenius_pt (Per.σA g) x

theorem map_mk_eq_zero {R : Type} [CommRing R] {m n : Type} (I : Ideal R) (M : Matrix m n R) :
    M.map (Ideal.Quotient.mk I) = 0 ↔ ∀ i j, M i j ∈ I := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]

theorem msub {R B : Type} [CommRing R] [CommRing B] {m n : Type} (f : R →+* B) (M M' : Matrix m n R) :
    (M - M').map f = M.map f - M'.map f := Matrix.map_sub _ (map_sub f) _ _

theorem map_smul_one {R B : Type} [CommRing R] [CommRing B] {n : Type} [DecidableEq n] (f : R →+* B) (a : R) :
    (a • (1 : Matrix n n R)).map f = f a • (1 : Matrix n n B) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, h]

theorem exists_of_mem_sup {R : Type} [CommRing R] {a b x : R} (h : x ∈ Ideal.span {a} ⊔ Ideal.span {b}) :
    ∃ u v, x = b * u + a * v := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  exact ⟨z, y, by ring⟩

theorem σA_mem (bk : BK K) (g : GQ l) (n M : ℕ) (a : Ainf l)
    (ha : a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M}) :
    Per.σA g a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hE : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  obtain ⟨w, hw⟩ := hE
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, hw, mul_pow]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)) (Ideal.mem_sup_right ?_)
  exact Ideal.mem_span_singleton.2 ⟨Per.σA g z * w ^ M, by ring⟩

theorem ev_mem (bk : BK K) (n M : ℕ) (s : bk.S) (hs : s ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ M}) :
    bk.ev s ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  have := Ideal.mem_map_of_mem bk.ev hs
  rwa [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow, map_pow,
    map_natCast] at this

end GlobalTheory.BKLim.DRLim

open GlobalTheory.BKLim.DRLim in

theorem GlobalTheory.BKLim.isDR_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsDR) → F₀.IsDR := by
  intro l _ K bk d N ρ tw F F₀ r hlink hDR M
  obtain ⟨c, hc⟩ := GlobalTheory.T.breuilKisin_beta_bounded_denominators l K bk (M + 1)
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_invariant_lift_mod_E l K bk (M + 1)
  choose γf hγ1 hγ2 using hk₀
  have htf1 := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1
  have htfM := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk (M + 1)
  let Xm : (Fin d × Fin d → bk.S) → Matrix (Fin d) (Fin d) bk.S := fun x => Matrix.of fun i j => x (i, j)
  let I₁ : ℕ → Ideal bk.S := fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ 1}
  let J : ℕ → Ideal (Ainf l) := fun n => Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ (M + 1)}
  let Φ : ↥(GK K) → Matrix (Fin d) (Fin d) bk.S → Matrix (Fin d) (Fin d) (Ainf l) := fun g β =>
    (F₀.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev
  let Q : ℕ → (Fin d × Fin d → bk.S) → Prop := fun n x =>
    (∀ i j, (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j ∈ I₁ n) ∧
      ∀ g i j, Φ g (Xm x) i j ∈ J n
  have hmono : ∀ n x, Q (n + 1) x → Q n x := by
    intro n x ⟨h1, h2⟩
    have hl : ∀ {R : Type} [CommRing R] (y : R), Ideal.span {(l : R) ^ (n + 1)} ≤ Ideal.span {(l : R) ^ n} :=
      fun _ => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))
    exact ⟨fun i j => sup_le_sup_right (hl (0 : bk.S)) _ (h1 i j),
      fun g i j => sup_le_sup_right (hl (0 : Ainf l)) _ (h2 g i j)⟩
  have hpert : ∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)}) →
      Q n y := by
    intro n x y ⟨h1, h2⟩ hd
    have hle : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} ≤ I₁ n :=
      sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega))) _
    have hD : ∀ i j, (Xm x - Xm y) i j ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} :=
      fun i j => hd (i, j)
    refine ⟨fun i j => ?_, fun g i j => ?_⟩
    · have e : (Xm y - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (Xm x - Xm y) i j := by
        simp only [Matrix.sub_apply]; ring
      rw [e]
      exact sub_mem (h1 i j) (hle (hD i j))
    · have e : Φ g (Xm y) = Φ g (Xm x) - ((F₀.ε g).map WittVector.frobenius *
          ((Xm x - Xm y).map bk.ev).map (Per.σA (g : GQ l)) - (Xm x - Xm y).map bk.ev) := by
        simp only [Φ, msub, Matrix.mul_sub]; abel
      rw [e, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply]
      refine sub_mem (h2 g i j) (sub_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) ?_)
      · exact σA_mem bk _ n (M + 1) _ (ev_mem bk n (M + 1) _ (hD k j))
      · exact ev_mem bk n (M + 1) _ (hD i j)
  have hex : ∀ n, ∃ x, Q n x := by
    intro n
    obtain ⟨m, hnm, R, G, hRT, hRG⟩ := hlink n
    obtain ⟨k', β'', hβ''⟩ := hDR m (M + 1)
    obtain ⟨β', hβ'⟩ := hc N (tw.d' m) _ (F m) k' β'' hβ''
    have hrel := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
      (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hRT
    let φS := frobS l bk.a
    let γ : Matrix (Fin (tw.d' m)) (Fin d) bk.S := Matrix.of fun i j => γf (φS (G i j))
    let Mx : Matrix (Fin d) (Fin d) bk.S := R.map φS * β' * γ
    refine ⟨fun ij => Mx ij.1 ij.2, ?_, ?_⟩
    ·
      let q := Ideal.Quotient.mk (I₁ n)
      have hE : ∀ s : bk.S, bk.E ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (by simpa using hs)))
      have hL : ∀ s : bk.S, (l : bk.S) ^ n ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 hs))
      have hq1 : β'.map q = q ((l : bk.S) ^ c) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) _) := by
        have : (β' - (l : bk.S) ^ c • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) bk.S)).map q = 0 := by
          ext i j; exact hE _ (hβ'.1 i j)
        rwa [msub, map_smul_one, sub_eq_zero] at this
      have hq2 : γ.map q = q ((l : bk.S) ^ k₀) • (G.map φS).map q := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, γ, smul_eq_mul, ← map_mul]
        exact (Ideal.Quotient.eq.2 (Ideal.Quotient.eq_zero_iff_mem.1 (hE _ (hγ1 _))))
      have hq3 : (R.map φS).map q * (G.map φS).map q = q ((l : bk.S) ^ r) • (1 : Matrix (Fin d) (Fin d) _) := by
        have : (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)).map (q.comp φS) = 0 := by
          ext i j
          refine hL _ ?_
          have := map_dvd φS (hRG i j)
          simpa [φS, map_pow, map_natCast] using this
        rw [msub, Matrix.map_mul, map_smul_one, sub_eq_zero, RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_map,
          Function.comp_apply, map_pow, map_natCast] at this
        rw [this, map_pow, map_natCast]
      refine (map_mk_eq_zero (I₁ n) _).1 ?_
      show (Mx - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)).map q = 0
      rw [msub, map_smul_one, Matrix.map_mul, Matrix.map_mul, hq1, hq2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [hq3, smul_smul, sub_eq_zero]
      congr 1
      simp only [← map_mul, ← pow_add]
      ring_nf
    · intro g
      refine (map_mk_eq_zero (J n) _).1 ?_
      let p := Ideal.Quotient.mk (J n)
      show (Φ g Mx).map p = 0
      have hp1 : ((F₀.ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p =
          ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p := by
        have h : (((F₀.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * (F m).ε g)).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ?_))
          simpa [map_pow, map_natCast] using map_dvd (WittVector.frobenius : Ainf l →+* Ainf l) (hrel g i j)
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp2 : (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * ((β'.map bk.ev).map (Per.σA (g : GQ l))).map p = (β'.map bk.ev).map p := by
        have h : ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l) * (β'.map bk.ev).map (Per.σA (g : GQ l)) - β'.map bk.ev)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hβ'.2 g i j)))
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp3 : ((γ.map bk.ev).map (Per.σA (g : GQ l))).map p = (γ.map bk.ev).map p := by
        ext i j
        simp only [Matrix.map_apply, Matrix.of_apply, γ]
        exact Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hγ2 _ g)))
      have hRev : (R.map φS).map bk.ev = (R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => bk.ev_frob _
      have hRσ : ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map (Per.σA (g : GQ l)) = ((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => σA_frob _ _
      simp only [Φ, Mx, msub, Matrix.map_mul]
      rw [hRev, hRσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hp1, Matrix.mul_assoc _ ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p), hp2, hp3, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness l K bk (Fin d × Fin d) (M + 1) Q hmono hpert hex
  refine ⟨c + k₀ + r, Xm x, fun i j => ?_, fun g i j => ?_⟩
  · have h4 := htf1.2.2.2 (bk.ev ((Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j))
      (fun n => exists_of_mem_sup (ev_mem bk n 1 _ ((hx n).1 i j)))
    simpa using htf1.2.1 _ h4
  · have h4 := htfM.2.2.2 (Φ g (Xm x) i j) (fun n => exists_of_mem_sup ((hx n).2 g i j))
    exact (pow_dvd_pow _ (Nat.le_succ M)).trans h4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrIsIntegralInvInFieldFactor
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem idem_mul_aeval_idem_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A) (p : R[X]) :
    f * aeval (f * w) p = f * aeval w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, mul_add, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, mul_pow]
    calc f * (algebraMap R A a * (f ^ n * w ^ n)) = algebraMap R A a * ((f * f ^ n) * w ^ n) := by ring
      _ = algebraMap R A a * (f * w ^ n) := by rw [← pow_succ', hf.pow_succ_eq]
      _ = f * (algebraMap R A a * w ^ n) := by ring

theorem isIntegral_idem_mul_of_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A)
    (h : IsIntegral R (Ideal.Quotient.mk (Ideal.span {1 - f}) w)) : IsIntegral R (f * w) := by
  obtain ⟨q, hq, hqw⟩ := h
  have h0 : aeval w q ∈ Ideal.span {1 - f} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← hqw, ← aeval_def]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ R (Ideal.span {1 - f})) w q).symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h0
  have h1 : f * aeval w q = 0 := by
    rw [hc, ← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul]
  refine ⟨X * q, monic_X.mul hq, ?_⟩
  rw [← aeval_def, map_mul, aeval_X, mul_assoc, mul_left_comm, idem_mul_aeval_idem_mul hf w q, h1, mul_zero]

theorem isIntegral_or_isIntegral_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  intro K B f y z hf hinv hyz
  by_cases hf0 : f = 0
  · left; rw [hf0, zero_mul]; exact isIntegral_zero
  set I : Ideal B.A := Ideal.span {1 - f} with hI
  have hmk : ∀ a b : B.A, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ ∃ c, a - b = (1 - f) * c := by
    intro a b
    rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    rfl
  have hf1 : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), hmk]
    exact ⟨-1, by ring⟩
  have hfm : ∀ a : B.A, Ideal.Quotient.mk I (f * a) = Ideal.Quotient.mk I a := by
    intro a; rw [map_mul, hf1, one_mul]
  have hfield : IsField (B.A ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hf0 ?_⟩, mul_comm, ?_⟩
    · obtain ⟨c, hc⟩ := (hmk 0 1).1 h
      have := congrArg (f * ·) hc
      simp only [mul_sub, mul_zero, mul_one, zero_sub] at this
      rw [← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul] at this
      simpa using this
    · intro a ha
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hfx : f * x ≠ 0 := by
        intro h0
        apply ha
        rw [← hfm x, h0, map_zero]
      obtain ⟨v, hv⟩ := hinv x hfx
      refine ⟨Ideal.Quotient.mk I v, ?_⟩
      rw [← map_mul, ← hfm (x * v), ← mul_assoc, hv, hf1]
  haveI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I hfield
  letI : Field (B.A ⧸ I) := Ideal.Quotient.field I
  haveI : CharZero K.O :=
    ⟨fun m n h => Nat.cast_injective (R := K.E) (by simpa using congrArg (algebraMap K.O K.E) h)⟩
  let e : FractionRing K.O ≃ₐ[K.O] K.E := IsLocalization.algEquiv (nonZeroDivisors K.O) (FractionRing K.O) K.E
  letI : Algebra (FractionRing K.O) (B.A ⧸ I) :=
    ((algebraMap K.E (B.A ⧸ I)).comp (e : FractionRing K.O →+* K.E)).toAlgebra
  haveI : IsScalarTower K.O (FractionRing K.O) (B.A ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change _ = algebraMap K.E (B.A ⧸ I) (e (algebraMap K.O (FractionRing K.O) x))
    rw [AlgEquiv.commutes]
    first
      | exact IsScalarTower.algebraMap_apply K.O K.E (B.A ⧸ I) x
      | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsIntegral (FractionRing K.O) (B.A ⧸ I) := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
    have := IsIntegral.map_of_comp_eq (e.symm : K.E →+* FractionRing K.O) (RingHom.id (B.A ⧸ I)) ?_ hx
    · simpa using this
    · ext t
      change algebraMap K.E (B.A ⧸ I) (e (e.symm t)) = _
      simp
  have hinv' : Ideal.Quotient.mk I (f * z) = (Ideal.Quotient.mk I (f * y))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← hfm, show f * (f * z * (f * y)) = f * y * z * f * f by ring, hyz, hf.eq, hf.eq, hf1]
  rcases GlobalTheory.LN.isIntegral_or_isIntegral_inv K.O (B.A ⧸ I) (Ideal.Quotient.mk I (f * y)) with h | h
  · left
    have := isIntegral_idem_mul_of_quot hf (f * y) h
    rwa [← mul_assoc, hf.eq] at this
  · right
    rw [← hinv'] at h
    have := isIntegral_idem_mul_of_quot hf (f * z) h
    rwa [← mul_assoc, hf.eq] at this

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SatInvUnit

theorem perfectRing_tilt_fraction_field (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ l fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
    simp [frobenius_def, div_pow, map_pow]⟩

theorem constantCoeff_frobW (l : ℕ) [Fact l.Prime] (x : WCb l) :
    WittVector.constantCoeff (frobW l x) = frobenius (Cb l) l (WittVector.constantCoeff x) :=
  WittVector.map_coeff (frobenius (Cb l) l) x 0

theorem constantCoeff_galW (l : ℕ) [Fact l.Prime] (g : GQ l) (x : WCb l) :
    WittVector.constantCoeff (galW l g x) = autCb l (galTilt l g) (WittVector.constantCoeff x) :=
  WittVector.map_coeff (autCb l (galTilt l g)).toRingHom x 0

end GlobalTheory.SatInvUnit

namespace GlobalTheory.SatInvUnit

theorem isUnit_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A →
    (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) →
    (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) →
    IsUnit Y := by
  intro l _ K bk d Y A hY hA hφ hg hsat
  haveI : PerfectRing (Cb l) l := perfectRing_tilt_fraction_field l
  set c : WCb l →+* Cb l := WittVector.constantCoeff (p := l) (R := Cb l) with hc

  have hdetA : IsUnit A.det := by
    obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y.det hY
    have h1 : frobW l Y.det = Y.det * A.det := by
      rw [← Matrix.det_mul, ← hφ]
      simpa using RingHom.map_det (frobW l).toRingHom Y
    have hlm : ((l : WCb l)) ^ m ≠ 0 := left_ne_zero_of_mul (hu ▸ hY)
    rw [hu, map_mul, map_pow, map_natCast, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hlm h1
    have hfu : IsUnit (frobW l (u : WCb l)) := u.isUnit.map (frobW l)
    rw [h2] at hfu
    exact isUnit_of_mul_isUnit_right hfu
  have hcA : (A.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdetA.map c).ne_zero
  by_cases h0 : (Y.map c).det = 0
  · exfalso
    have hAm : ∀ i j, (A.map c) i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) :=
      fun i j => Subring.mem_map.2 ⟨A i j, hA i j, rfl⟩
    have hφ' : (Y.map c).map (frobenius (Cb l) l) = Y.map c * A.map c := by
      have : (Y.map (frobW l)).map c = (Y.map c).map (frobenius (Cb l) l) := by
        ext i j
        exact constantCoeff_frobW l (Y i j)
      rw [← this, hφ, Matrix.map_mul]
    have hg' : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧
        R * (Y.map c).map (autCb l (galTilt l (g : GQ l))) = Y.map c := by
      intro g hfix
      obtain ⟨R, hR, hRY⟩ := hg g hfix
      refine ⟨R.map c, hR.map c.mapMatrix, ?_⟩
      have : (Y.map (galW l (g : GQ l))).map c = (Y.map c).map (autCb l (galTilt l (g : GQ l))) := by
        ext i j
        exact constantCoeff_galW l (g : GQ l) (Y i j)
      rw [← this, ← Matrix.map_mul, hRY]
    obtain ⟨vb, hv0, hvm, hYv⟩ := GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable l K bk d (Y.map c) (A.map c) hcA hAm hφ' hg' h0
    choose v hv hvc using fun i => Subring.mem_map.1 (hvm i)
    have hdiv : ∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i := by
      intro i
      rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
      change c (Y.mulVec v i) = 0
      rw [RingHom.map_mulVec]
      have : (c ∘ v) = vb := funext fun j => hvc j
      rw [this, hYv]
      rfl
    apply hv0
    funext i
    obtain ⟨r, hr⟩ := hsat v hv hdiv i
    rw [← hvc i, hr, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
    rfl
  · have hu : IsUnit Y.det := by
      apply WittVector.isUnit_of_coeff_zero_ne_zero
      intro h
      apply h0
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact h
    exact (Matrix.isUnit_iff_isUnit_det Y).2 hu

end GlobalTheory.SatInvUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem jumps_exact_adm : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F := by
  intro D HW F
  exact ⟨fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL,
    fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCoverStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_stratifiedSolution_succ_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  first | exact @GlobalTheory.BSP.lift_solution_succ | exact GlobalTheory.BSP.lift_solution_succ | (intros; apply GlobalTheory.BSP.lift_solution_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_breuilKisin_basis_invariant_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  first | exact @GlobalTheory.LimBasis.main | exact GlobalTheory.LimBasis.main | (intros; apply GlobalTheory.LimBasis.main; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBoundsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkN_along_family_of_localBounds : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  first | exact @GlobalTheory.LinkFam.main | exact GlobalTheory.LinkFam.main | (intros; apply GlobalTheory.LinkFam.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProofStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCountDirectLifting_proof : StepLocDirect := by
  first | exact @GlobalTheory.Pass.LocDirect.main | exact GlobalTheory.Pass.LocDirect.main | (intros; apply GlobalTheory.Pass.LocDirect.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansionStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachN_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | exact GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinJumpSumLeOfPowMemOfInertiaEqTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.min_jumpSum_le_jumpSum_of_totally_ramified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  first | exact @GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top | exact GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top | (intros; apply GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top <;> assumption)
end

