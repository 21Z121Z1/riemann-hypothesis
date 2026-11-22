import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RationalFormValues
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev lamV (D : D7) (i : Fin D.R.m) : D.what₂.Tau → DomWeight (Vc D i).rank :=
  fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ

def IsCoefExt {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K')
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) (c' : VV K' lam →ₛₗ[σ'] W) : Prop :=
  ∀ (v : VV K lam) (v' : VV K' lam), (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) → c' v' = c₀ v

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def formFn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def ValuesIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ (x : A.fam.amb.FL i t) (h : Bridge.Gf (Vc D i)), ∃ v : VV K' (lamV D i), c' v = formFn R i t x h

def RationalValuesAt (R : RealDat D A Ks) : Prop :=
  ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (lamV D i) →ₛₗ[D.what₂.embLL] (R.cV i).coef.W),
    Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (lamV D) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (t : T) (K' : Type) [Field K'] (ι : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp ι = D.what₂.embLL →
      ∀ c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W, IsCoefExt (W := (R.cV i).W) ι (lamV D i) (c0L i) c' → ValuesIn R i t c'

theorem ValuesIn.reps {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    {c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W} (H : ValuesIn R i t c') {J : Subgroup (Bridge.Gf (Vc D i))} {Cl : Type}
    {y : Cl → Bridge.Gf (Vc D i)} (_hy : Bridge.IsReps (Bridge.ratF (Vc D i)) J y) (x : A.fam.amb.FL i t) :
    ∃ val : Cl → VV K' (lamV D i), ∀ k, c' (val k) = formFn R i t x (y k) :=
  ⟨fun k => (H x (y k)).choose, fun k => (H x (y k)).choose_spec⟩

end Row

def RationalValues : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → RationalValuesAt R

end GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SublevelSplitting
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def matF (V : HSp D) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Units.val (h : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))

def compAtPl (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (matF V h).map (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E))

variable (D) in

def IsSplitPl (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧ P.under (𝓞 D.host.F) = v ∧ P'.under (𝓞 D.host.F) = v

def SuppSplitOff (V : HSp D) (bad : ℕ) (h : Bridge.Gf V) : Prop :=
  ∃ Sp : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v ∈ Sp, IsSplitPl D v ∧ (bad : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, v ∉ Sp → compAtPl V v h = 1

def IsTransl (V : HSp D) (Λ : Lat V) (h : Bridge.Gf V) (L : Lat V) : Prop :=
  ∀ x : Fin V.rank → D.host.E, x ∈ L ↔
    (matF V h⁻¹).mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))

def IsOpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) : Prop :=
  IsOpen ((J'.comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V))

def IsSubLev (V : HSp D) (J J' : Subgroup (Bridge.Gf V)) (vol : ℝ) : Prop :=
  J' ≤ J ∧ J'.relIndex J ≠ 0 ∧ IsOpenLev V J' ∧ vol = ((J'.relIndex J : ℕ) : ℝ)⁻¹

def IsAdReps (V : HSp D) (Λ : Lat V) (J' : Subgroup (Bridge.Gf V)) (bad : ℕ) {n : ℕ} (h : Fin n → Bridge.Gf V)
    (Lh : Fin n → Lat V) (gam : Fin n → ℕ) : Prop :=
  Bridge.IsReps (Bridge.ratF V) J' h ∧ (∀ a, SuppSplitOff V bad (h a)) ∧ (∀ a, IsTransl V Λ (h a) (Lh a)) ∧
    ∀ a, Finite (Bridge.stab (Bridge.ratF V) J' (h a)) ∧ gam a = Nat.card (Bridge.stab (Bridge.ratF V) J' (h a))

def IsLatReps (V : HSp D) (Λ : Lat V) (bad : ℕ) {n : ℕ} (Lh : Fin n → Lat V) : Prop :=
  (∀ a, Submodule.IsLattice D.host.E (Lh a) ∧ Formalism.L2.Herm.dualL D.sp.cm V (Lh a) = Lh a ∧
    ∃ M : ℕ, 0 < M ∧ M.Coprime bad ∧ (∀ x ∈ Λ, (M : D.host.E) • x ∈ Lh a) ∧ ∀ x ∈ Lh a, (M : D.host.E) • x ∈ Λ) ∧
  ∀ (g : Bridge.Gf V) (L : Lat V), IsTransl V Λ g L →
    ∃ (a : Fin n) (γ : GL (Fin V.rank) D.host.E), γ ∈ UR D.sp.cm V.gram ∧
      ∀ x, x ∈ Lh a ↔ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L

variable {T : Type}

def levJ (L : LevCh D T) (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J

def IsBad (L : LevCh D T) (t : T) (bad : ℕ) : Prop :=
  0 < bad ∧ ∀ PP : Pl D.host.E, PP ∈ L.Pg ∨ PP ∈ L.Q t → (bad : 𝓞 D.host.E) ∈ PP.asIdeal

def RepsAt (L : LevCh D T) (i : Fin D.R.m) (t : T) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → Bridge.Gf (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ) (Lh : Fin n → Lat (Vc D i))
    (gam : Fin n → ℕ) (vol : ℝ),
    IsBad L t bad ∧ N ∣ bad ∧ IsSubLev (Vc D i) (levJ L i t) J' vol ∧
      IsAdReps (Vc D i) (L.ΛV i) J' bad h Lh gam ∧ IsLatReps (Vc D i) (L.ΛV i) bad Lh

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowAt (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → RealDat.models_vpos (D := D) →
    ∀ (i : Fin D.R.m) (t : T) (N : ℕ), 0 < N → RepsAt R.toLevCh i t N

def RowPlainAt (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → RealDat.models_vpos (D := D) → ∀ (i : Fin D.R.m) (t : T), RepsAt R.toLevCh i t 1

theorem RowAt.plain {R : RealDat D A Ks} (h : RowAt R) : RowPlainAt R :=
  fun hL hp i t => h hL hp i t 1 Nat.one_pos

end Row

def Row : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), RowAt R

theorem IsSubLev.vol_pos {V : HSp D} {J J' : Subgroup (Bridge.Gf V)} {vol : ℝ} (h : IsSubLev V J J' vol) :
    0 < vol ∧ vol ≤ 1 := by
  obtain ⟨_, h2, _, rfl⟩ := h
  have h1 : (1 : ℝ) ≤ ((J'.relIndex J : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h2
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h1⟩

theorem IsAdReps.pos {V : HSp D} {Λ : Lat V} {J' : Subgroup (Bridge.Gf V)} {bad n : ℕ} {h : Fin n → Bridge.Gf V}
    {Lh : Fin n → Lat V} {gam : Fin n → ℕ} (H : IsAdReps V Λ J' bad h Lh gam) : (∀ a, 0 < gam a) ∧ 0 < n := by
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨hf, e⟩ := H.2.2.2 a
    rw [e]; exact Nat.card_pos
  · obtain ⟨a, _⟩ := H.1 1
    exact a.pos

end GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)

variable {D : D7}

abbrev Place (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev ModHost (D : D7) : Type := ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E

def conjIdeal (H : ModHost D) (I : Ideal (𝓞 D.host.E)) : Ideal (𝓞 D.host.E) :=
  I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

def PrimeToAA (D : D7) (P : Place D) : Prop := FractionalIdeal.count D.host.E P D.host.AA = 0

structure IsDesignLevel (P : Formalism.L2.Host.PiBar D.host) (H : ModHost D) (l : Level H) : Prop where
  root : (H.rt : D.host.E) = D.host.sqrtMinusD
  level : l.M = D.host.g 0 * D.host.g 1
  half : l.Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

structure TwistGuard (D : D7) (Q : Finset (Place D)) : Prop where
  onePrime : ∀ P ∈ Q, ∀ P' ∈ Q, ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P.asIdeal → (q : 𝓞 D.host.E) ∈ P'.asIdeal →
    P.under (𝓞 D.host.K) = P'.under (𝓞 D.host.K)
  primeToC : ∀ P ∈ Q, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

structure IsCoverHalf {H : ModHost D} (l : Level H) (Q : Finset (Place D)) (n : ℕ) (I : Ideal (𝓞 D.host.E))
    (l₂ : Level H) : Prop where
  squarefree : Squarefree n
  primes : ∀ q : ℕ, q.Prime → (q ∣ n ↔ ∃ P ∈ Q, (q : 𝓞 D.host.E) ∈ P.asIdeal)
  coprime : Nat.Coprime n l.M
  level : l₂.M = l.M * n
  aux : l₂.A = l.A
  half : l₂.Mb = l.Mb * I
  norm : I * conjIdeal H I = Ideal.span {(n : 𝓞 D.host.E)}
  conj_coprime : I ⊔ conjIdeal H I = ⊤
  places_dvd : ∀ P ∈ Q, P.asIdeal ∣ I

def AAPrimeToLevel {H : ModHost D} (l : Level H) : Prop :=
  ∀ P : Place D, (P.asIdeal ∣ l.Mb ∨ P.asIdeal ∣ conjIdeal H l.Mb) → PrimeToAA D P

def HalvesAt {H : ModHost D} (l : Level H) (Pg Q : Finset (Place D)) : Prop :=
  l.Mb = ∏ P ∈ Pg, P.asIdeal ∧
    ∃ (n : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Level H), IsCoverHalf l Q n I l₂ ∧ AAPrimeToLevel l₂

def HalfOfLevelAndCover : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 →
    ∀ (H : ModHost D) (l : Level H), IsDesignLevel L.C.P H l →
      ∀ t : T, TwistGuard D (L.Q t) → HalvesAt l L.Pg (L.Q t)

def HalfOfLevelAndCoverReal : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ C : Core D, LawsM C → C.pb = R.C.P.pb →
      ∀ t : T, TwistGuard D (R.Q t) → HalvesAt C.Q.l R.Pg (R.Q t)

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro hz
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · rw [FractionalIdeal.coeIdeal_eq_zero] at h1
    unfold Formalism.BasicNotions.Host.ccE at h1
    rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h1
    exact D.host.ccK_ne_bot h1
  · rw [inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero] at h1
    have h2 := D.host.𝔟_spec.2
    rw [h1] at h2
    simp at h2

theorem IsCoverHalf.dvd {H : ModHost D} {l l₂ : Level H} {Q : Finset (Place D)} {n : ℕ} {I : Ideal (𝓞 D.host.E)}
    (h : IsCoverHalf l Q n I l₂) : l.Dvd l₂ := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd
  refine ⟨⟨n, h.level⟩, ?_, ?_⟩
  · rw [h.half]
    intro x hx
    exact (Submodule.mem_inf.mp (Ideal.mul_le_inf hx)).1
  · rw [h.aux]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeightFlagWeyl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightFlagWeyl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Extremal

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsWeylK (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Prop := ∀ a, ε (s a) = ε a

def IsFlagWeyl (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Prop :=
  IsWeylK ε s ∧ (∀ a b, a < b → ε a = true → ε b = true → s a < s b) ∧
    ∀ a b, a < b → ε a = false → ε b = false → s b < s a

def IsExtremalUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧
    ∃ s : Equiv.Perm (Fin n), IsWeylK ε s ∧ IsWtOn (Formalism.REAL.Kset ε) σ (Formalism.QuantumDeterminants.lowK ε lam ∘ s) w

def IsFrameExtremalUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) :
    Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧
    ∃ s : Equiv.Perm (Fin n), IsFlagWeyl ε s ∧ IsWtOn (Formalism.REAL.Kset ε) σ (Formalism.QuantumDeterminants.lowK ε lam ∘ s) w

theorem IsFrameExtremalUnit.extremal {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H} (h : IsFrameExtremalUnit ε lam σ w) :
    IsExtremalUnit ε lam σ w :=
  ⟨h.1, h.2.1, h.2.2.imp fun _ hs => ⟨hs.1.1, hs.2⟩⟩

example : IsFlagWeyl ![true, false, false] (Equiv.swap (1 : Fin 3) 2) := by
  unfold IsFlagWeyl IsWeylK; decide

example : ¬ IsFlagWeyl ![true, false, false] (1 : Equiv.Perm (Fin 3)) := by
  unfold IsFlagWeyl IsWeylK; decide

end Extremal

variable {D : D7}

section Source

variable {V : HSp D} (θ : InfFam D) (c : CoefA V) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)

def IsWtSrc (ν : Fin V.rank → ℝ) (w : c.W) : Prop :=
  ∀ x : Fin V.rank → ℝ,
    c.ρ (atTau θ V τ (B * Matrix.diagonal (fun a => Complex.exp ((x a : ℂ) * Complex.I)) * B⁻¹)) w =
      Complex.exp (((∑ a, ν a * x a : ℝ) : ℂ) * Complex.I) • w

def IsLowestSrc (w : c.W) : Prop :=
  ∃ ν, IsWtSrc θ c B τ ν w ∧ ∀ (μ : Fin V.rank → ℝ) (u : c.W), u ≠ 0 → IsWtSrc θ c B τ μ u → CDom (allPos _) ν μ

end Source

def IsHarmonic {m n : ℕ} (p : D.what₂.Tau → ℕ) (P : PolF D m n) : Prop :=
  ∀ τ (a b : Fin m), (a : ℕ) < p τ → p τ ≤ (b : ℕ) →
    ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def IoExtAt (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  ∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
    (∀ ρ, IsFrameExtremalUnit ((R.MW i (sg0 D A)).ε ρ) ((R.MW i (sg0 D A)).lam ρ) ((R.MW i (sg0 D A)).σ ρ)
      ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)) ∧
    ‖w‖ = 1 ∧ R.ioP i (PiTensorProduct.tprod ℂ v) w = RealDat.Delta i

def IoExtFullAt (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  (∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
    (∀ ρ, IsFrameExtremalUnit ((R.MW i (sg0 D A)).ε ρ) ((R.MW i (sg0 D A)).lam ρ) ((R.MW i (sg0 D A)).σ ρ)
      ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)) ∧
    ‖w‖ = 1 ∧ (∀ τ, IsLowestSrc R.θ (R.cV i) (R.BV i τ) τ w) ∧
    R.ioP i (PiTensorProduct.tprod ℂ v) w = RealDat.Delta i) ∧
  IsHarmonic (fun τ => ((Wc D i).sig (tauE D τ)).1) (RealDat.Delta i)

def IoExtremal (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ i, IoExtAt R i

def IoExtremalFull (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ i, IoExtFullAt R i

end GlobalTheory.IndefiniteRowSideFullHecke.WeightFlagWeyl

end
end

