import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RbarData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

def ssRep {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k :=
  Classical.epsilon fun ρ' : Γ →* GL (Fin a) k => IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
    ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly

def BcGood (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧ ∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = Rw.locR σ w

open Classical in

def bcOf (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Multiset (ℕ × ℕ) :=
  if h : ∃ Sig, BcGood D Rw σ Sig then Multiset.ofList (h.choose.map fun p => (p.a, p.d)) else {(D.R.r, 1)}

def RbarData {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) : Prop :=
  ∃ i : X.nd.Loc, X.nd.w i = lam ∧ ∃ (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)),
    HasParamW X.nd Y.naut i σ Sig ∧ IsRepOfSig X.nd Y.naut i Sig ρ

open Classical in

def rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    G D.host.E X.nd.Om →* GL (Fin D.R.r) (Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam)) :=
  if h : RbarData Y σ lam then
    ssRep (mapRep (((fbCast (h.choose_spec.1 ▸ X.nd.w_l h.choose).symm (X.nd.lPrime h.choose).out
        (D.what₂.places.resChar_prime lam)).toRingHom.comp
      ((Y.naut.kFbar h.choose).comp (IsLocalRing.residue (X.nd.O h.choose))))) h.choose_spec.2.choose_spec.choose)
  else 1

def mtSup {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (i : X.nd.Loc) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i)) :=
  ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧
      IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P

def castMt {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j)) :
    Submodule ℂ (D.what₂.Mt μ' j') := by
  subst h1; subst h2; exact M

open Classical in

def mtParOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (μ : D.what₂.Tup) (j : ℕ) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  if h : ∃ i, X.nd.mu i = μ ∧ X.nd.j i = j then castMt h.choose_spec.1 h.choose_spec.2 (mtSup Y h.choose σ') else ⊥

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameAtOfLocalizationEq
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

noncomputable section

namespace GlobalTheory.SameAtOfLoc

theorem exists_smul_mem_of_le_locP {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (𝓞 E) W] (Q : HeightOneSpectrum (𝓞 E)) {A B : Submodule (𝓞 E) W} (hA : A.FG)
    (h : A ≤ localization₂ Q.asIdeal B) : ∃ s ∉ Q.asIdeal, ∀ x ∈ A, s • x ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  have key : ∃ s ∉ Q.asIdeal, ∀ a ∈ S, s • a ∈ B := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Formalism.L2.DIV.lc_one_notMem Q, by simp⟩
    | insert a S ha ih =>
      obtain ⟨s, hs, hS⟩ := ih (le_trans (Submodule.span_mono (by
        rw [Finset.coe_insert]; exact Set.subset_insert _ _)) h)
      obtain ⟨t, ht, hta⟩ := (Formalism.L2.DIV.lc_mem_locP Q B a).1
        (h (Submodule.subset_span (by simp)))
      refine ⟨t * s, Formalism.L2.DIV.lc_mul_notMem Q ht hs, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact B.smul_mem s hta
      · rw [mul_smul]; exact B.smul_mem t (hS b hb)
  obtain ⟨s, hs, hS⟩ := key
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact B.smul_mem r hx

end GlobalTheory.SameAtOfLoc

namespace GlobalTheory

open GlobalTheory.SameAtOfLoc in

theorem sameAt_of_localized_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A →
    Submodule.IsLattice E B → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B → SameAt Q A B := by
  intro E _ _ _ n Q A B hA hB h
  obtain ⟨a, ha, h1⟩ := exists_smul_mem_of_le_locP Q hB.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q B)
  obtain ⟨a', ha', h2⟩ := exists_smul_mem_of_le_locP Q hA.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q A)
  exact ⟨a, ha, a', ha', h1, h2⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
section
noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx.VacEqPf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

variable {D : D7} {X : Fields} (s : Seam D X)

theorem star_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def vec {n : ℕ} (x : Sp X.E n) : Fin n → D.host.E := fun i => s.iE (x i)

theorem int_iff (z : X.E) : s.iE z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ z ∈ (algebraMap (𝓞 X.E) X.E).range := by
  have h1 : ∀ w : D.host.E, w ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  have h2 : ∀ w : X.E, w ∈ (algebraMap (𝓞 X.E) X.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 X.E)).symm
  rw [h1, h2]
  constructor
  · intro h
    have := map_isIntegral_int s.iE.symm.toRingHom h
    simpa using this
  · intro h
    exact map_isIntegral_int s.iE.toRingHom h

theorem vec_add {n : ℕ} (x y : Sp X.E n) : vec s (x + y) = vec s x + vec s y := by
  funext i
  simp [vec]

theorem vec_smulE {n : ℕ} (c : X.E) (x : Sp X.E n) : vec s (c • x) = s.iE c • vec s x := by
  funext i
  simp [vec]

theorem vec_smulO {n : ℕ} (r : 𝓞 X.E) (r' : 𝓞 D.host.E) (h : s.iE (r : X.E) = (r' : D.host.E)) (x : Sp X.E n) : vec s (r • x) = r' • vec s x := by
  funext i
  show s.iE ((r • x) i) = (r' • vec s x) i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  show s.iE (r : X.E) * _ = (r' : D.host.E) * _
  rw [h]
  rfl

theorem vec_span {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span (𝓞 X.E) T) :
    vec s x ∈ Submodule.span (𝓞 D.host.E) (vec s '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : vec s (0 : Sp X.E n) = 0 := by funext i; simp [vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vec_add s]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr'⟩ := (int_iff s (r : X.E)).2 ⟨r, rfl⟩
    rw [vec_smulO s r r' hr'.symm]
    exact Submodule.smul_mem _ _ hx

theorem vec_spanE {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span X.E T) :
    vec s x ∈ Submodule.span D.host.E (vec s '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : vec s (0 : Sp X.E n) = 0 := by funext i; simp [vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vec_add s]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [vec_smulE s]; exact Submodule.smul_mem _ _ hx

theorem vec_surj {n : ℕ} (y : Fin n → D.host.E) : vec s (fun i => s.iE.symm (y i) : Sp X.E n) = y := by
  funext i
  simp [vec]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) : y ∈ s.lat N ↔ ∃ x ∈ N, vec s x = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y h => exact h
    | zero => exact ⟨0, N.zero_mem, by funext i; simp [vec]⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      exact ⟨x + x', N.add_mem hx hx', vec_add s x x'⟩
    | smul r y _ hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨r₀, hr₀⟩ := (int_iff s (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
      refine ⟨r₀ • x, N.smul_mem _ hx, vec_smulO s r₀ r ?_ x⟩
      show s.iE (algebraMap (𝓞 X.E) X.E r₀) = _
      rw [hr₀]
      simp
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem stdH_vec (hok : s.Ok) {n : ℕ} (x y : Sp X.E n) :
    (letI := D.host.cmStar; stdH D.host.E n (vec s x) (vec s y)) = s.iE (hStd X.E n x y) := by
  show ∑ i, (letI := D.host.cmStar; star (s.iE (x i))) * s.iE (y i) = s.iE (∑ i, star (x i) * y i)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hok.2, star_conj]

theorem sd_lat (hok : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (letI := D.host.cmStar; IsSDLat D.host.E n (s.lat N)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hN.1.fg
    have h : s.lat N = Submodule.span (𝓞 D.host.E) (vec s '' (S : Set (Sp X.E n))) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact vec_span s _ (by rw [hS]; exact hx)
      · refine Submodule.span_mono (Set.image_mono ?_)
        rw [← hS]
        exact Submodule.subset_span
    rw [h]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [eq_top_iff]
    intro y _
    have h1 : (fun i => s.iE.symm (y i) : Sp X.E n) ∈ Submodule.span X.E (N : Set (Sp X.E n)) := by
      rw [hN.1.span_eq_top]; trivial
    have h2 := vec_spanE s _ h1
    rw [vec_surj s] at h2
    exact Submodule.span_mono (fun z hz => Submodule.subset_span hz) h2
  · intro y
    constructor
    · intro hy x hx
      obtain ⟨y₀, hy₀, rfl⟩ := (mem_lat s N y).1 hy
      obtain ⟨x₀, hx₀, rfl⟩ := (mem_lat s N x).1 hx
      rw [stdH_vec s hok, int_iff s]
      have h1 : y₀ ∈ dual (hStd X.E n) N := by rw [hN.2]; exact hy₀
      exact Submodule.mem_one.1 ((mem_dual N y₀).1 h1 x₀ hx₀)
    · intro h
      refine (mem_lat s N y).2 ⟨fun i => s.iE.symm (y i), ?_, vec_surj s y⟩
      have hd : IsUnimodular (hStd X.E n) N := hN.2
      unfold IsUnimodular at hd
      rw [← hd, mem_dual]
      intro x₀ hx₀
      have h1 := h (vec s x₀) ((mem_lat s N _).2 ⟨x₀, hx₀, rfl⟩)
      rw [← vec_surj s y, stdH_vec s hok, int_iff s] at h1
      exact Submodule.mem_one.2 h1

def matOf {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  fun i j => s.iE (γ (Pi.single j 1) i)

theorem apply_eq_sum {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (x : Sp X.E n) (i : Fin n) :
    γ x i = ∑ j, γ (Pi.single j 1) i * x j := by
  have h : x = ∑ j, x j • (Pi.single j 1 : Sp X.E n) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem matOf_mulVec {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (x : Sp X.E n) :
    (matOf s γ).mulVec (vec s x) = vec s (γ x) := by
  funext i
  show ∑ j, s.iE (γ (Pi.single j 1) i) * s.iE (x j) = s.iE (γ x i)
  rw [apply_eq_sum γ x i, map_sum]
  simp only [map_mul]

theorem smulLat_matOf {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    (letI := D.host.cmStar; SDLat.smulLat (matOf s γ) (s.lat N)) = s.lat (gmap γ N) := by
  ext y
  rw [mem_lat s]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_lat s N w).1 hw
    exact ⟨γ x, ⟨x, hx, rfl⟩, (matOf_mulVec s γ x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨vec s x, (mem_lat s N _).2 ⟨x, hx, rfl⟩, matOf_mulVec s γ x⟩

theorem symm_single {n : ℕ} (γ : UF X.E n) (i k : Fin n) :
    γ.1.symm (Pi.single k 1) i = star (γ.1 (Pi.single i 1) k) := by
  have h : ∑ l, star (γ.1 (Pi.single i 1) l) * γ.1 (γ.1.symm (Pi.single k 1)) l =
      ∑ l, star ((Pi.single i 1 : Sp X.E n) l) * γ.1.symm (Pi.single k 1) l := γ.2 (Pi.single i 1) (γ.1.symm (Pi.single k 1))
  rw [LinearEquiv.apply_symm_apply] at h
  simpa [Pi.single_apply, apply_ite star] using h.symm

theorem matOf_unitary (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    letI := D.host.cmStar
    matOf s γ.1 ∈ Matrix.unitaryGroup (Fin n) D.host.E := by
  letI := D.host.cmStar
  rw [Matrix.mem_unitaryGroup_iff']
  refine Matrix.ext fun i j => ?_
  have h1 := stdH_vec s hok (γ.1 (Pi.single i 1)) (γ.1 (Pi.single j 1))
  rw [γ.2] at h1
  have h2 : hStd X.E n (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
    show ∑ l, star ((Pi.single i 1 : Sp X.E n) l) * (Pi.single j 1 : Sp X.E n) l = _
    simp [Pi.single_apply, apply_ite star, eq_comm]
  rw [h2] at h1
  rw [Matrix.one_apply]
  have h3 : s.iE (if i = j then 1 else 0) = if i = j then 1 else 0 := by split_ifs <;> simp
  rw [h3] at h1
  exact h1

theorem vacEq_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → B.EqP χ → Even a → Even b → VacEq (ambOf s B χ cD) a b := by
  intro D X s cc δ B χ cD a b hok hE ha hb γ γ' N N' hN hN' z
  letI := D.host.cmStar
  have h := hE.1 a b ⟨s.lat N, sd_lat s hok hN⟩ ⟨s.lat N', sd_lat s hok hN'⟩ ha hb
    ⟨matOf s γ.1, matOf_unitary s hok γ⟩ ⟨matOf s γ'.1, matOf_unitary s hok γ'⟩
  have h1 := smulLat_matOf s γ.1 N
  have h2 := smulLat_matOf s γ'.1 N'
  show B.eNat χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) (fun τ => z (s.iT.symm τ)) =
    B.eNat χ a b (s.lat N) (s.lat N') (fun τ => (ambOf s B χ cD : Amb X).pullV a b γ.1 γ'.1 z (s.iT.symm τ))
  rw [← h1, ← h2]
  refine (congrFun h _).symm.trans ?_
  show B.eNat χ a b (s.lat N) (s.lat N') _ = _
  congr 1
  funext τ i j
  show ∑ l, (∑ k, star (TaylorLogMetric.embT D τ (s.iE (γ'.1 (Pi.single i 1) k))) * z (s.iT.symm τ) k l) * TaylorLogMetric.embT D τ (s.iE (γ.1 (Pi.single j 1) l)) =
    ∑ k : Fin b, ∑ l : Fin a, s.σ₀ (X.emb (s.iT.symm τ) (γ'.1.symm (Pi.single k 1) i)) * z (s.iT.symm τ) k l *
      s.σ₀ (X.emb (s.iT.symm τ) (γ.1 (Pi.single j 1) l))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hok.1, hok.1, Equiv.apply_symm_apply, symm_single, hok.2,
    show ∀ x, TaylorLogMetric.embT D τ (D.host.conj x) = starRingEnd ℂ (TaylorLogMetric.embT D τ x) from
      D.host.conjE_apply (TaylorLogMetric.embT D τ)]
  rfl

end GlobalTheory.Mem.Col2.JetEx.VacEqPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAtZeroFree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem frm_free_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K (R.N 0) Pr.vGs) (hΛ : Λ = colLev Ch 0) (Θ : LevQFam X.E X.K (R.N 0) Q) (g : FrmG Λ Θ)
    (p : DecoF X.E (R.N 0) (Pr.vT u) Pr.vGs Q) (hp : FrmG.incl Λ Θ g • p = p) : g = 1 := by
  subst hΛ
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (g.2.1 : GLG X.E (R.N 0) Pr.vGs) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp g.2.1.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  have ha : ((g.1, (g.2.1 : GLG X.E (R.N 0) Pr.vGs)) : UF X.E (R.N 0) × GLG X.E (R.N 0) Pr.vGs) • p.deco = p.deco :=
    congrArg DecoF.deco hp
  have h1 : ((g.1, (g.2.1 : GLG X.E (R.N 0) Pr.vGs)) : UF X.E (R.N 0) × GLG X.E (R.N 0) Pr.vGs) = 1 :=
    DecoSet.decoration_stabilizer_trivial_unipotent hX hPr p.deco ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
      (isNilpotent_of_mem_HX_zero hN.le hmem)
  apply GlobalTheory.FramedForms.incl_injective
  rw [map_one]
  exact GlobalTheory.FramedForms.stab_inj p hp (one_smul _ p) (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp h1).2

theorem stepAt_zero_free {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hL : ∀ b, L.levG 0 b = colLev Ch 0) :
    (stepAt sel mu cst L Tp u 0).Free := by
  intro b g d hd
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hΛ : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
    obtain ⟨b, hb⟩ := b
    obtain ⟨b0, rfl⟩ := Option.isSome_iff_exists.mp (hb.mpr hm)
    exact hL b0
  exact frm_free_zero Ch hX hPr hbig u _ hΛ _ g d.1.1 (congrArg (fun x => x.1.1) hd)

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmodulePatchAtPrimeIsLatticeLocP
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.InertExchange

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem patchAt_commens (A B : Submodule (𝓞 E) (Sp E n)) (hA : Submodule.IsLattice E A)
    (hB : Submodule.IsLattice E B) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ (∀ x ∈ A, d • x ∈ B) ∧ (∀ x ∈ B, d • x ∈ A) := by
  obtain ⟨a, ha, hA1, hA2⟩ := Formalism.L2.DIV.lc_sandwich A hA
  obtain ⟨b, hb, hB1, hB2⟩ := Formalism.L2.DIV.lc_sandwich B hB
  refine ⟨a * b, mul_ne_zero ha hb, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_comm, mul_smul]
    exact hB2 _ (hA1 x hx)
  · rw [mul_smul]
    exact hA2 _ (hB1 x hx)

theorem patchAt_isLattice_locP (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) :
    Submodule.IsLattice E A → Submodule.IsLattice E B → Submodule.IsLattice E (patchAt P A B) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro hA hB
  obtain ⟨d, hd, hAB, hBA⟩ := patchAt_commens A B hA hB
  let Λ : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) (Sp E n) := fun Q => localization₂ Q.asIdeal (if Q = P then A else B)
  have hcl : ∀ Q, localization₂ Q.asIdeal (Λ Q) = Λ Q := fun Q => Formalism.L2.DIV.localized_localized Q _
  have h1 : ∀ Q, ∀ x ∈ Λ Q, d • x ∈ localization₂ Q.asIdeal B := by
    intro Q x hx
    by_cases hQ : Q = P
    · subst hQ
      simp only [Λ, if_true] at hx
      obtain ⟨s, hs, hsx⟩ := hx
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact hAB _ hsx
    · simp only [Λ, hQ, if_false] at hx
      exact Submodule.smul_mem _ d hx
  have h2 : ∀ Q, ∀ x ∈ B, d • x ∈ Λ Q := by
    intro Q x hx
    by_cases hQ : Q = P
    · simp only [Λ, hQ, if_true]
      exact Formalism.L2.DIV.lc_le_locP _ _ (hBA x hx)
    · simp only [Λ, hQ, if_false]
      exact Formalism.L2.DIV.lc_le_locP _ _ (B.smul_mem d hx)
  have hpat : patchAt P A B = ⨅ Q, Λ Q := rfl
  refine ⟨?_, fun Q => ?_⟩
  · have hdE : (algebraMap (𝓞 E) E d) ≠ 0 := by
      intro h
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h, map_zero]))
    have hmem : ∀ x ∈ B, d • x ∈ patchAt P A B := by
      intro x hx
      rw [hpat, Submodule.mem_iInf]
      exact fun Q => h2 Q x hx
    have hle : ∀ x ∈ patchAt P A B, d • x ∈ B := by
      intro x hx
      rw [hpat, Submodule.mem_iInf] at hx
      have : Submodule.span (𝓞 E) {d • x} ≤ B :=
        Formalism.L2.DIV.lc_le_of_le_locP fun Q => by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact h1 Q x (hx Q)
      exact this (Submodule.subset_span rfl)
    let f : Sp E n →ₗ[𝓞 E] Sp E n := d • LinearMap.id
    have hf : Function.Injective f := by
      intro x y hxy
      have e : algebraMap (𝓞 E) E d • x = algebraMap (𝓞 E) E d • y := by
        simpa [f, algebraMap_smul] using hxy
      exact smul_right_injective _ hdE e
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hB.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · rw [eq_top_iff, ← hB.span_eq_top, Submodule.span_le]
      intro y hy
      have hy' : y = (algebraMap (𝓞 E) E d)⁻¹ • (d • y) := by
        rw [← algebraMap_smul E d y, smul_smul, inv_mul_cancel₀ hdE, one_smul]
      rw [hy']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem y hy))
  · rw [hpat]
    exact Formalism.L2.DIV.localized_iInf Λ B d hd hcl h1 h2 Q

end GlobalTheory.InertExchange
end

