import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
section
noncomputable section

namespace GlobalTheory.SWQ

open scoped TensorProduct NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def qd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u : Fin N → R) : R :=
  ∑ l, algebraMap F R (a l) * u l ^ 2

def Bd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u u' : Fin N → R) : R :=
  ∑ l, algebraMap F R (2 * a l) * u l * u' l

def rat (ξ : Fin N → F) : Fin N → AF F := fun l => algebraMap F (AF F) (ξ l)

def inf (u : Fin N → AF F) : Fin N → Ainf F := fun l => fstA F (u l)

def fin (u : Fin N → AF F) : Fin N → Af F := fun l => sndA F (u l)

def loc (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → Af F) : Fin N → Fv F v := fun l => evalV F v (u l)

def re (x : Ainf F) (w : InfinitePlace F) : ℝ :=
  (InfinitePlace.Completion.extensionEmbedding w (x w)).re

def sz (u : Fin N → AF F) : ℝ := ∑ l, ∑ w : InfinitePlace F, |re (inf u l) w|

def hf (F : Type) [Field F] [NumberField F] : AF F := pairA F (algebraMap F (Ainf F) (1 / 2)) 1

def intN (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) : Set (Fin N → Fv F v) :=
  {u | ∀ l, u l ∈ v.adicCompletionIntegers F}

def Decay (Φ : (Fin N → AF F) → ℂ) : Prop :=
  Continuous Φ ∧ (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ u, fin u ∉ K → Φ u = 0) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ u, ‖Φ u‖ * (1 + sz u) ^ k ≤ C

def IsCov1 (ν : Measure (AF F)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ D : Set (AF F), MeasurableSet D ∧
    IsAddFundamentalDomain (algebraMap F (AF F)).range.toAddSubgroup D ν ∧ ν D = 1

def muV (N : ℕ) (ν : Measure (AF F)) : Measure (Fin N → AF F) := Measure.pi fun _ => ν

def IsLam (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) : Prop :=
  (∀ w, lam w ≠ 0) ∧ ∀ x : Ainf F,
    psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, lam w * re x w : ℝ) : ℂ))

def Ctx (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F) : Prop :=
  IsTotallyReal F ∧ IsCharAF F ψ ∧ IsLam ψ lam ∧ IsCov1 ν ∧ ∀ l, a l ≠ 0

variable (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F)

def Ub (b : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => ψ (b * qd (AF F) a u) * Φ u

def Da (t : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => Φ (t • u)

def Fo (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ∫ s, Φ s * ψ (Bd (AF F) a s u) ∂(muV N ν)

def rho (x y : Fin N → AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) * Φ (u + x)

def th (Φ : (Fin N → AF F) → ℂ) : ℂ := ∑' ξ : Fin N → F, Φ (rat ξ)

def Fst (Φ : (Fin N → AF F) → ℂ) (b : AF F) : ℂ := ∫ u, Φ u * ψ (b * qd (AF F) a u) ∂(muV N ν)

def dens (Φ : (Fin N → AF F) → ℂ) (y : AF F) : ℂ := ∫ b, Fst ψ ν a Φ b * ψ (-(b * y)) ∂ν

def Eis (Φ : (Fin N → AF F) → ℂ) : ℂ := Φ 0 + ∑' b : F, Fst ψ ν a Φ (algebraMap F (AF F) b)

def gauss (τ : InfinitePlace F → ℂ) (x : Fin N → Ainf F) : ℂ :=
  ∏ w : InfinitePlace F, ∏ l, Complex.exp
    (2 * Real.pi * Complex.I *
        ((lam w * re (algebraMap F (Ainf F) (a l)) w * (τ w).re * re (x l) w ^ 2 : ℝ) : ℂ) -
      ((2 * Real.pi * |lam w * re (algebraMap F (Ainf F) (a l)) w| * (τ w).im * re (x l) w ^ 2 : ℝ) : ℂ))

def GG (τ : InfinitePlace F → ℂ) (Φ : (Fin N → AF F) → ℂ) : Prop :=
  (∀ w, 0 < (τ w).im) ∧ ∃ Φf : (Fin N → Af F) → ℂ, IsSB Φf ∧ ∀ u, Φ u = gauss lam a τ (inf u) * Φf (fin u)

def mob (g : Matrix (Fin 2) (Fin 2) (AF F)) (w : InfinitePlace F) : ℂ :=
  ((re (fstA F (g 0 0)) w : ℂ) * Complex.I + (re (fstA F (g 0 1)) w : ℂ)) /
    ((re (fstA F (g 1 0)) w : ℂ) * Complex.I + (re (fstA F (g 1 1)) w : ℂ))

def Rel (L : AddSubgroup (Fin N → Af F)) (n₀ : ℝ) (g : Matrix (Fin 2) (Fin 2) (AF F))
    (Φ : (Fin N → AF F) → ℂ) : Prop :=
  g.det = 1 ∧ GG lam a (mob g) Φ ∧ ∫ u, ‖Φ u‖ ^ 2 ∂(muV N ν) = n₀ ∧
    ∀ x y : Fin N → AF F, inf x = 0 → inf y = 0 → fin (g 0 0 • x + g 1 0 • y) ∈ L →
      fin (g 0 1 • x + g 1 1 • y) ∈ L → rho ψ a x y Φ = Φ

def Htf (b : Af F) : ℝ := ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖evalV F v b‖

def Ht (b : AF F) : ℝ := (∏ w : InfinitePlace F, max 1 |re (fstA F b) w|) * Htf (sndA F b)

structure IsTheta (M : ℕ) (Θ : Measure (Fin N → AF F)) : Prop where
  ratl : Θ {u | ¬ ∃ β : F, qd (AF F) a u = algebraMap F (AF F) β} = 0
  small : ∀ Ω : Set (Fin N → AF F), IsCompact Ω → ∃ C : ℝ≥0, ∀ j : ℕ,
    Θ ((fun u => hf F ^ j • u) '' Ω) * 2 ^ (Fintype.card (InfinitePlace F) * M * j) ≤ C
  big : ∀ Ω : Set (Fin N → AF F), IsCompact Ω → ∃ C : ℝ≥0, ∀ j : ℕ,
    Θ {u | hf F ^ j • u ∈ Ω} ≤ C * 2 ^ (Fintype.card (InfinitePlace F) * N * j)
  four : ∀ Φ, Decay Φ → Decay (Fo ψ ν a Φ) →
    Fo ψ ν a Φ 0 + ∫ u, Fo ψ ν a Φ u ∂Θ = Φ 0 + ∫ u, Φ u ∂Θ
  dil : ∀ t : F, t ≠ 0 → Θ.map (fun u => algebraMap F (AF F) t • u) = Θ

def Dif (Θ : Measure (Fin N → AF F)) (Φ : (Fin N → AF F) → ℂ) : ℂ :=
  Φ 0 + ∫ u, Φ u ∂Θ - Eis ψ ν a Φ

def PureV (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin N → Fv F v) → ℂ) : Prop :=
  (∀ v, IsSB (Φv v)) ∧ ∀ᶠ v in Filter.cofinite, Φv v = (intN N v).indicator 1

def tens (Φi : (Fin N → Ainf F) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin N → Fv F v) → ℂ) :
    (Fin N → AF F) → ℂ := fun u => Φi (inf u) * ∏ᶠ v, Φv v (loc v (fin u))

def IsPM (μ : Measure (Fin N → AF F)) (μi : Measure (Fin N → Ainf F))
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin N → Fv F v)) : Prop :=
  (∀ᶠ v in Filter.cofinite, μv v (intN N v) = 1) ∧
    ∀ Φi Φv, Integrable Φi μi → PureV Φv → Integrable (tens Φi Φv) μ ∧
      ∫ u, tens Φi Φv u ∂μ = (∫ x, Φi x ∂μi) * ∏ᶠ v, ∫ x, Φv v x ∂(μv v)

def IsPM1 (ν : Measure (AF F)) (νi : Measure (Ainf F))
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) : Prop :=
  (∀ᶠ v in Filter.cofinite, νv v (v.adicCompletionIntegers F : Set (Fv F v)) = 1) ∧
    ∀ (Ui : Set (Ainf F)) (Uv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), IsCompact Ui →
      (∀ v, IsCompact (Uv v) ∧ IsOpen (Uv v)) →
      (∀ᶠ v in Filter.cofinite, Uv v = (v.adicCompletionIntegers F : Set (Fv F v))) →
      ν {y | fstA F y ∈ Ui ∧ ∀ v, evalV F v (sndA F y) ∈ Uv v} = νi Ui * ∏ᶠ v, νv v (Uv v)

structure LocData where
  μi : Measure (Fin N → Ainf F)
  νi : Measure (Ainf F)
  μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin N → Fv F v)
  νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)
  fi : Ainf F → Measure (Fin N → Ainf F)
  fv : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin N → Fv F v)
  sdμi : SelfDual μi fun x y => psiInf F ψ (Bd (Ainf F) a x y)
  sdνi : SdR (Ainf F) (psiInf F ψ) νi
  sdμv : ∀ v, SelfDual (μv v) fun x y => psiV F ψ v (Bd (Fv F v) a x y)
  sdνv : ∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)
  fibi : IsFibreFamily μi (qd (Ainf F) a) id Set.univ νi {c : Ainf F | ∀ w, c w ≠ 0} fi
  fibv : ∀ v, IsFibreFamily (μv v) (qd (Fv F v) a) id Set.univ (νv v) {c | c ≠ 0} (fv v)

variable {ψ a}

def IsXV (T : LocData ψ a) (β : F) (m : Measure (Fin N → AF F)) : Prop :=
  m {u | qd (AF F) a u ≠ algebraMap F (AF F) β} = 0 ∧
    ∀ Φi Φv, Continuous Φi → HasCompactSupport Φi → PureV Φv → Integrable (tens Φi Φv) m ∧
      Multipliable (fun v => ∫ x, Φv v x ∂(T.fv v (algebraMap F (Fv F v) β))) ∧
      ∫ u, tens Φi Φv u ∂m = (∫ x, Φi x ∂(T.fi (algebraMap F (Ainf F) β))) *
        ∏' v, ∫ x, Φv v x ∂(T.fv v (algebraMap F (Fv F v) β))

def Good (ψ : AddChar (AF F) ℂ) (a : Fin N → F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔
    y ∈ v.adicCompletionIntegers F) ∧
  ‖(2 : Fv F v)‖ = 1 ∧ ∀ l, ‖algebraMap F (Fv F v) (a l)‖ = 1

section Herm

variable {E : Type} [Field E] [Algebra F E] {M : ℕ}

def emb (R : Type) [CommRing R] [Algebra F R] (w : Fin N → Fin M → E) (u : Fin N → R) :
    Fin 1 → Fin M → R ⊗[F] E := fun _ i => ∑ l, u l ⊗ₜ[F] w l i

def IsOB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (a : Fin N → F) (w : Fin N → Fin M → E) : Prop :=
  (∀ l, a l ≠ 0) ∧ LinearIndependent F w ∧ Submodule.span F (Set.range w) = ⊤ ∧
    ∀ ξ : Fin N → F, hE σ J (∑ l, ξ l • w l) (∑ l, ξ l • w l) = algebraMap F E (qd F a ξ)

def orbM (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin 1 → Fin M → E)) : Measure (Fin 1 → Fin M → AF F ⊗[F] E) :=
  Measure.sum fun ξ : S =>
    (μ.restrict 𝓕).map fun h => h⁻¹ • ratTup (F := F) (AF F) (ξ : Fin 1 → Fin M → E)

def thW (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) : Measure (Fin 1 → Fin M → AF F ⊗[F] E) :=
  (μ 𝓕)⁻¹ • orbM σ J μ 𝓕 {ξ | ξ ≠ 0}

end Herm

theorem decay_zero : Decay (fun _ : Fin N → AF F => (0 : ℂ)) :=
  ⟨continuous_const, ⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => ⟨0, fun _ => by simp⟩⟩

end GlobalTheory.SWQ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotMtStableOfFree
section
noncomputable section

namespace GlobalTheory.EX.DQ.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField

theorem goodAllAt_iff (D : D7) (C : NChoice D) (I : TwIn D) : GoodAllAt D C I ↔ GlobalTheory.TwAll.TwGoodAtAll D C I := by
  have h : ∀ (a : ℤ) (l : ℕ), Nat.Coprime a.natAbs l ↔ IsCoprime a (l : ℤ) := fun a l => by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  simp only [GoodAllAt, GlobalTheory.TwAll.TwGoodAtAll, h]

theorem exps (D : D7) (i : D.ntw.Tw) :
    ¬ Nat.Coprime (0 : ℤ).natAbs (D.ntw.l i) ∧ Nat.Coprime (-1 : ℤ).natAbs (D.ntw.l i) :=
  ⟨by simpa using (D.ntw.lPrime i).out.ne_one, by simp⟩

theorem tup_setDiv (D : D7) (N) (h) : TupUsedAt (setDiv D N h) ↔ TupUsedAt D := Iff.rfl
theorem mt_setDiv (D : D7) (N) (h) : MtStableAt (setDiv D N h) ↔ MtStableAt D := Iff.rfl
theorem conj_setDiv (D : D7) (O : Obj D) (N) (h) : TwConjAt (setDiv D N h) (O.tr N h).nch ↔ TwConjAt D O.nch := Iff.rfl
theorem av_setDiv (D : D7) (N) (h) : AvRec (setDiv D N h) = AvRec D := rfl
theorem ok_setDiv (D : D7) (N) (h) (I : TwIn D) (i) : TwIn.Ok (D := setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i ↔ I.Ok i := Iff.rfl
set_option maxHeartbeats 2000000 in
theorem one_setDiv (D : D7) (N) (h) (I : TwIn D) (i b Q k ψ) : TwGoodOne (setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i b Q k ψ ↔ TwGoodOne D I i b Q k ψ := Iff.rfl

theorem tup_finite {D : D7} (h : TupUsedAt D) (hf : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite) : Finite D.what₂.Tup := by
  have : (Set.univ : Set D.what₂.Tup) ⊆ insert D.what₂.mu0 (insert D.what₂.muStar (insert D.what₂.muStar'
      (D.what₂.muAt '' {w | D.what₂.muAt w ≠ D.what₂.mu0}))) := by
    intro μ _
    rcases h μ with h | h | h | ⟨w, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · by_cases h0 : D.what₂.muAt w = D.what₂.mu0
      · exact Or.inl (h.trans h0)
      · exact Or.inr (Or.inr (Or.inr ⟨w, h0, h.symm⟩))
  exact Set.finite_univ_iff.1 ((((hf.image _).insert _).insert _).insert _ |>.subset this)

section Lat

variable {O L V : Type} [CommRing O] [Field L] [NumberField L] [AddCommGroup V] [Module ℂ V] {φ : O →+* ℂ}

theorem mem_carrier_iff (M : Rows.OLat O φ V) (x : V) :
    x ∈ M.carrier ↔ x ∈ AddSubgroup.closure {y | ∃ c : O, ∃ v ∈ M.gen, y = φ c • v} := by
  classical
  constructor
  · rintro ⟨c, rfl⟩
    exact sum_mem fun v hv => AddSubgroup.subset_closure ⟨c v, v, hv, rfl⟩
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, v, hv, rfl⟩ := hy
      refine ⟨Pi.single v c, ?_⟩
      rw [Finset.sum_eq_single v (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => absurd hv h)]
      simp
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩
    | neg a _ ha =>
      obtain ⟨c, rfl⟩ := ha
      exact ⟨-c, by simp⟩

open Classical in

def sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : Rows.OLat O φ V where
  gen := (Finset.univ ×ˢ M.gen).image fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2
  span_top := by
    rw [eq_top_iff, ← M.span_top, Submodule.span_le]
    intro v hv
    obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) := (RingOfIntegers.basis L).index_nonempty
    have h0 : σ (RingOfIntegers.basis L i : L) ≠ 0 := by
      rw [map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
      exact (RingOfIntegers.basis L).ne_zero i
    have := Submodule.smul_mem (Submodule.span ℂ (((Finset.univ ×ˢ M.gen).image
      fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2 : Finset V) : Set V)) (σ (RingOfIntegers.basis L i : L))⁻¹
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩)))
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

theorem smul_mem_sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) (a : 𝓞 L) (c : O) {v : V} (hv : v ∈ M.gen) :
    (φ c * σ (a : L)) • v ∈ (sat σ M).carrier := by
  classical
  rw [mem_carrier_iff]
  have e : (φ c * σ (a : L)) • v = ∑ i, φ (((RingOfIntegers.basis L).repr a i : ℤ) * c) •
      σ (RingOfIntegers.basis L i : L) • v := by
    conv_lhs => rw [← (RingOfIntegers.basis L).sum_repr a]
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  rw [e]
  exact sum_mem fun i _ => AddSubgroup.subset_closure
    ⟨_, _, Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩, rfl⟩

theorem subset_sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : M.carrier ⊆ (sat σ M).carrier := by
  intro x hx
  rw [mem_carrier_iff] at hx ⊢
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨c, v, hv, rfl⟩
  have := smul_mem_sat σ M 1 c hv
  rw [mem_carrier_iff] at this
  simpa using this

theorem sat_stable (σ : L →+* ℂ) (M : Rows.OLat O φ V) (a : 𝓞 L) : ∀ y ∈ (sat σ M).carrier,
    σ (a : L) • y ∈ (sat σ M).carrier := by
  classical
  intro y hy
  rw [mem_carrier_iff] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, w, hw, rfl⟩ := hy
    obtain ⟨⟨i, v⟩, hv, rfl⟩ := Finset.mem_image.1 hw
    have := smul_mem_sat σ M (a * RingOfIntegers.basis L i) c (Finset.mem_product.1 hv).2
    convert this using 1
    simp [smul_smul, mul_left_comm]
  | zero => rw [mem_carrier_iff]; simp
  | add x y _ _ hx hy => rw [mem_carrier_iff] at *; rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mem_carrier_iff] at *; rw [smul_neg]; exact neg_mem hx

theorem range_of_stable (σ : L →+* ℂ) (M : Rows.OLat O φ V) (hli : LinearIndependent ℂ (fun v : M.gen => (v : V)))
    {v : V} (hv : v ∈ M.gen) (a : 𝓞 L) (h : ∀ y ∈ M.carrier, σ (a : L) • y ∈ M.carrier) : σ (a : L) ∈ Set.range φ := by
  classical
  have h1 : v ∈ M.carrier := (mem_carrier_iff M v).2 (AddSubgroup.subset_closure ⟨1, v, hv, by simp⟩)
  obtain ⟨c, hc⟩ := h v h1
  have := Fintype.linearIndependent_iff.1 hli (fun w => φ (c w) - (Pi.single v (σ (a : L)) : V → ℂ) w) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [Finset.sum_coe_sort M.gen (fun w => φ (c w) • w), ← hc,
      Finset.sum_coe_sort M.gen (fun w => (Pi.single v (σ (a : L)) : V → ℂ) w • w),
      Finset.sum_eq_single v (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => absurd hv h)]
    simp) ⟨v, hv⟩
  exact ⟨c v, by simpa [sub_eq_zero] using this⟩

end Lat

set_option maxHeartbeats 4000000 in

def setMt (D : D7) (M : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (D.what₂.Amb μ)) : D7 :=
  { D with
    what₂ := { D.what₂ with Mtilde := M }
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

def satRec (D : D7) : D7 := setMt D fun μ => sat D.what₂.embLL (D.what₂.Mtilde μ)

theorem mtStable_sat (D : D7) : MtStableAt (satRec D) :=
  fun (μ : D.what₂.Tup) a y hy => sat_stable D.what₂.embLL (D.what₂.Mtilde μ) a y hy

theorem tup_setMt (D : D7) (M) : TupUsedAt (setMt D M) ↔ TupUsedAt D := Iff.rfl

theorem qd_sat (D : D7) (h : TupUsedAt D) (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0)
    (O : Obj (satRec D)) : QD (satRec D) O :=
  ⟨(tup_setMt D _).2 h, twAllAt_of_untwisted _ _ hu, mtStable_sat D⟩

theorem not_mtStable_of_free (D : D7) (μ : D.what₂.Tup)
    (hli : LinearIndependent ℂ (fun v : (D.what₂.Mtilde μ).gen => (v : D.what₂.Amb μ))) (hne : (D.what₂.Mtilde μ).gen.Nonempty)
    (a : 𝓞 D.what₂.LL) (ha : (a : D.what₂.LL) ∉ Set.range D.what₂.OtoLL) : ¬ MtStableAt D := fun h => by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨c, hc⟩ := range_of_stable D.what₂.embLL (D.what₂.Mtilde μ) hli hv a (h μ a)
  exact ha ⟨c, D.what₂.embLL.injective hc⟩

theorem used_muTw {D : D7} (h : TupUsedAt D) (w) : DV.Used D (D.what₂.muTw w) := h _

set_option maxHeartbeats 2000000 in
theorem good_setDiv (D : D7) (O : Obj D) (N) (h) (N0 S) :
    GoodAllAt (setDiv D N h) (O.tr N h).nch ⟨twEOf (O.tr N h).xd, N0, S⟩ ↔ GoodAllAt D O.nch ⟨twEOf O.xd, N0, S⟩ :=
  forall_congr' fun w => forall_congr' fun _ => and_congr (ok_setDiv D N h ⟨twEOf O.xd, N0, S⟩ (O.nch.twI w))
    (forall_congr' fun a => forall_congr' fun _ =>
      one_setDiv D N h ⟨twEOf O.xd, N0, S⟩ (O.nch.twI w) (O.nch.sd w) (O.nch.Q w) (O.nch.k' w) (O.nch.psi' w ^ a))

theorem qd_setDiv (D : D7) (O : Obj D) (N) (h) : QD (setDiv D N h) (O.tr N h) ↔ QD D O :=
  and_congr (tup_setDiv D N h) (and_congr (and_congr (conj_setDiv D O N h)
    (exists_congr fun N0 => exists_congr fun S => good_setDiv D O N h N0 S)) (mt_setDiv D N h))

theorem not_class_of_false {eps : ℝ} (Fm : FamP eps) : ¬ cls7 (fun _ _ => False) Fm := fun h =>
  (Fm.toFamCore.exists_pt 0).elim fun x hx =>
    hx.2.2.2.elim fun i => familyClass_points_satisfy_objectProperty _ Fm h x hx.2.1 i

theorem twGood_of_twAllF {eps : ℝ} {Fm : FamP eps} (h : TwAllF Fm) : TwGood Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨hc, N0, S, hS⟩ := h x hx hx1 i
  exact ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, by simpa using (hS w hw).2 1 (by simp)⟩⟩

theorem duty_of_duty7 {eps : ℝ} {Fm : FamP eps} (h : Duty7 Fm) : DC.Duty Fm :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end GlobalTheory.EX.DQ.Model

end
end

