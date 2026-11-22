import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal TensorProduct

abbrev RCosets {G G' : Type} [Group G] [Group G'] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotMeasure {G G' : Type} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G']
    (j : G' →* G) (μ : Measure G) (μ' : Measure G') (ν : Measure (RCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂μ = ∫⁻ c : RCosets j, ∫⁻ h, f (j h * c.out) ∂μ' ∂ν

example {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) :
    IsQuotMeasure (1 : PUnit →* G) μ (Measure.dirac PUnit.unit)
      (μ.map (Quotient.mk (QuotientGroup.rightRel (1 : PUnit →* G).range))) := by
  intro f hf
  have hout : ∀ g : G,
      (Quotient.mk (QuotientGroup.rightRel (1 : PUnit →* G).range) g).out = g := by
    intro g
    have h := Quotient.mk_out (s := QuotientGroup.rightRel (1 : PUnit →* G).range) g
    rw [QuotientGroup.rightRel_apply] at h
    obtain ⟨u, hu⟩ := h
    have h1 : (1 : G) = g * (Quotient.mk (QuotientGroup.rightRel (1 : PUnit →* G).range) g).out⁻¹ := by
      simpa using hu
    exact (mul_inv_eq_one.1 h1.symm).symm
  have hm : Measurable fun c : RCosets (1 : PUnit →* G) => f c.out := by
    rw [measurable_from_quotient]
    have : ((fun c : RCosets (1 : PUnit →* G) => f c.out) ∘ Quotient.mk'') = f := by
      funext g; exact congrArg f (hout g)
    rw [this]; exact hf
  simp only [MonoidHom.one_apply, one_mul, lintegral_const, measure_univ, mul_one]
  rw [lintegral_map hm measurable_quotient_mk'']
  exact lintegral_congr fun g => (congrArg f (hout g)).symm

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coords (W : HSpace E) (x : W.V) : Fin 1 → Fin W.rank → E := fun _ i => W.frame.repr x i

end Coord

def latTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator (fun _ => (1 : ℝ≥0∞)) (projFin X 0) *
    Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (y : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) y)

def IsInfQuotIntegral (D : D7) : letI := D.host.cmStar; ∀ (W : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_x : W.V) (_Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞)
    (_I : ℝ≥0∞), Prop :=
  letI := D.host.cmStar
  fun W P Q P' Q' x Φi I =>
  AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
    ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
  AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
  let xr : D.what₂.Tau → (Fin P ⊕ Fin Q → ℂ) :=
    fun ρ => A ρ *ᵥ fun i => embOf D ρ (coords W x 0 i)
  AllSome (fun C : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ =>
    ∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
      ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ xr ρ = 0) fun C =>
  AllSome (fun j : (D.what₂.Tau → UpqT P' Q') →* (D.what₂.Tau → UpqT P Q) =>
    ∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
      UpqT.mat (j b ρ) *ᵥ xr ρ = xr ρ) fun j =>
  AllSome (fun o : (D.what₂.Tau → UpqT P Q) →
      (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    ∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ xr ρ) fun o =>
  AllSome (IsQuotMeasure j (Measure.pi fun _ => D.cd.cd P Q) (Measure.pi fun _ => D.cd.cd P' Q'))
    fun ν => ∫⁻ c : RCosets j, Φi (o c.out) ∂ν = I

def HidaSetting {E : Type} [Field E] [NumberField E] [StarRing E] (W W' : HSpace E)
    (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[E] W.V) : Prop :=
  W.SigOK ∧ (∀ τ, W.sig τ = (P, Q)) ∧ 3 ≤ W.rank ∧
  (if s then P = P' + 1 ∧ Q = Q' else P = P' ∧ Q = Q' + 1) ∧
  W.hT x x = (if s then 1 else -1) ∧ x ∈ W.L0 ∧
  HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧
  W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q'))

def UnfoldAt (D : D7) : letI := D.host.cmStar; ∀ (W _W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_s : Bool) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' s x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
  ∀ (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
  ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
    ∃ I : ℝ≥0∞, IsInfQuotIntegral D W P Q P' Q' x Φi I ∧
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
        atInv D.sp.cm.sig W.gram (latTensor (L0c D W) Φi) h (coords W x'.1) ∂μ = μ' 𝓕' * I

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → (∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
    UnfoldAt D W W' P Q P' Q' s x

def UnfoldingAnyLattice (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → UnfoldAt D W W' P Q P' Q' s x

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

def stabRow {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (φ : n → A) :
    Subgroup (GL n A) where
  carrier := {g | φ ᵥ* (g : Matrix n n A) = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : φ ᵥ* (a : Matrix n n A) = φ := ha
    have hb' : φ ᵥ* (b : Matrix n n A) = φ := hb
    show φ ᵥ* ((a * b : GL n A) : Matrix n n A) = φ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha', hb']
  inv_mem' := by
    intro g hg
    have hg' : φ ᵥ* (g : Matrix n n A) = φ := hg
    show φ ᵥ* ((g⁻¹ : GL n A) : Matrix n n A) = φ
    conv_lhs => rw [← hg']
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

example {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] :
    stabRow (0 : n → A) = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  show (0 : n → A) ᵥ* (g : Matrix n n A) = 0
  simp

example : (-1 : GL (Fin 1) ℚ) ∉ stabRow (fun _ : Fin 1 => (1 : ℚ)) := by
  intro h
  have h' : (fun _ : Fin 1 => (1 : ℚ)) ᵥ* ((-1 : GL (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ) =
      fun _ => 1 := h
  have := congrFun h' 0
  simp [Matrix.vecMul, dotProduct] at this
  norm_num at this

section Local

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def toIntV : 𝓞 E →+* intV E v :=
  ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E v)
    (fun a => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E a, ⟨a, rfl⟩⟩, rfl⟩))

variable {E} {n : Type}

abbrev latV (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

variable {v}

def pr₁ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).1

def pr₂ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).2

def IsSplitting (σ : E →ₐ[F] E) (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  P ≠ Pb ∧
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * Pb.asIdeal ∧
  (∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) ∧
  (∀ x, x ∈ intV E v ↔
    (s x).1 ∈ v.adicCompletionIntegers F ∧ (s x).2 ∈ v.adicCompletionIntegers F) ∧
  (∀ a : 𝓞 E, a ∈ P.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1) ∧
  (∀ a : 𝓞 E, a ∈ Pb.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1)

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev baseDual (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def OverAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) : Prop :=
  ∃ (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),

    IsSplitting sp.cm.sig P Pb s ∧

    (∀ x : latV v (baseDual L), pr₁ s (x : Fin R.k → _) = 0 → L.fT v hv x = 0) ∧

    (∀ x : latV v (baseDual L),
      L.fT v hv x = 0 ↔ pr₁ s (x : Fin R.k → _) ∈ pr₁ s '' (latV v L.Lb : Set (Fin R.k → _))) ∧

    Nonempty ((latV v (baseDual L) ⧸ (latV v L.Lb).submoduleOf (latV v (baseDual L))) ≃ₗ[intV E v]
      ((intV E v ⧸ P.asIdeal.map (toIntV E v)) × (intV E v ⧸ Pb.asIdeal.map (toIntV E v)))) ∧

    pr₁ s '' (latV v N : Set (Fin R.k → _)) = pr₁ s '' (latV v (baseDual L) : Set (Fin R.k → _)) ∧
    pr₂ s '' (latV v N : Set (Fin R.k → _)) = pr₂ s '' (latV v L.Lb : Set (Fin R.k → _)) ∧

    (∃ hle : latV v N ≤ latV v (baseDual L),
      (L.fT v hv).comp (Submodule.inclusion hle) ≠ 0 ∧
      L.Uloc v = levelVL sp.cm.sig sp.gram0 v N ⊓
        stabFun (latV v N) ((L.fT v hv).comp (Submodule.inclusion hle))) ∧

    ∃ (h : GL (Fin R.k) (v.adicCompletion F))
      (φ : Fin R.k → v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
      (e : L.fM v hv ≃+
        v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)),
      pr₁ s '' (latV v N : Set (Fin R.k → _)) =
        Set.range (fun y : Fin R.k → v.adicCompletionIntegers F =>
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ fun i => (y i : v.adicCompletion F)) ∧
      Set.BijOn (fun g : GL (Fin R.k) (E ⊗[F] v.adicCompletion F) =>
          h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h)
        (levelVL sp.cm.sig sp.gram0 v N)
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range ∧
      φ ≠ 0 ∧
      (∀ (x : latV v (baseDual L)) (y : Fin R.k → v.adicCompletionIntegers F),
        pr₁ s (x : Fin R.k → _) =
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ (fun i => (y i : v.adicCompletion F)) →
        e (L.fT v hv x) = ∑ i, φ i * Ideal.Quotient.mk _ (y i)) ∧
      ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
        g ∈ L.Uloc v ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h ∈
          congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (stabRow φ)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧
  Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧
  (N : Set (Fin R.k → E)) ⊆ dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb ∧
  (∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → latV v N = latV v L.Lb) ∧
  (∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal), OverAt L N v hv) ∧
  L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def OverLatticeAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T →
    (∀ i : Fin 2, (D.mem u).A.T ≠ D.host.g i) ∧
    ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsOverLattice (Lv u) N

def OverLattice : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), OverLatticeAt D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    (N : Set (n → E)) = dualSet σ J N

def IsSelfDualDefiniteLattice (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N

def stabHat (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def levelU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  (Lv u).U

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N →
      levelU D Lv u ≤ stabHat D N →
      (((levelU D Lv u).relIndex (stabHat D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def StabiliserLevelIndexFormula : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

def ExistsOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), SplitsF D (D.mem u).A.T →
    ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N ∧
      (letI := D.host.cmStar; (Lv u).Lb) ≤ N ∧ levelU D Lv u ≤ stabHat D N

theorem factorT_pos (D : D7) (u : D.what₂.Word) :
    0 < (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
  have hk : D.R.k ≠ 0 := by
    have := D.R.m_add_three_le_k
    omega
  have hTk : (1 : ℝ) < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ hT hk
  exact pow_pos (by linarith) _

theorem stabHat_le (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    letI := D.host.cmStar
    stabHat D N ≤ UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  intro g hg
  unfold stabHat levelAfL level at hg
  exact (Subgroup.mem_inf.mp hg).1

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualStabiliserIndex
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    dualSet σ J N = (N : Set (n → E))

def stabK (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k)
      (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
      IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N →
      (Lv u).U ≤ stabK D N →
      (((Lv u).U.relIndex (stabK D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def IndexKU : Prop := ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

def ExistsSelfDualOver : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    SplitsF D (D.mem u).A.T →
      ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
        IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N ∧ (Lv u).Lb ≤ N ∧
        (Lv u).U ≤ stabK D N

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureLatticeIndependence
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def withLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def HasSignatureEverywhere (W : HSpace E) (P Q : ℕ) : Prop :=
  W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsIsometry (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  HSpace.IsIsomEmb W₁ W₂ e.toLinearMap

def CarriesLattice (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

def frameMatrix (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e.toLinearMap

example (W : HSpace E) : withLattice W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular = W := rfl

example (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : (withLattice W L hL hU).gram = W.gram := rfl

example (W : HSpace E) : IsIsometry W W (LinearEquiv.refl E W.V) ∧ CarriesLattice W W (LinearEquiv.refl E W.V) ∧
    frameMatrix W W (LinearEquiv.refl E W.V) = 1 :=
  ⟨fun _ _ => rfl, fun _ => Iff.rfl, by simp [frameMatrix]⟩

end Spaces

def Intertwines {A : Type} [CommRing A] {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) A)
    (g₁ : Matrix (Fin M₁) (Fin M₁) A) (g₂ : Matrix (Fin M₂) (Fin M₂) A) : Prop :=
  g₂ * C = C * g₁

def pointMatrix {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (HA.mat R σ J h).val

def baseChange {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) E) : Matrix (Fin M₂) (Fin M₁) (R ⊗[F] E) :=
  C.map (inclR R)

def IsConjugationBy {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M₁ M₂ : ℕ} (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E)
    (C : Matrix (Fin M₂) (Fin M₁) E) (Φ : HA R σ J₁ → HA R σ J₂) : Prop :=
  ∀ h : HA R σ J₁, Intertwines (baseChange R C) (pointMatrix R σ J₁ h) (pointMatrix R σ J₂ (Φ h))

example {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsConjugationBy R σ J J 1 id := by
  intro h
  rw [Intertwines, baseChange, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.one_mul]
  rfl

def LatticeIndependence (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W P Q →
    ∀ (L L' : Submodule (𝓞 D.host.E) W.V)
      (hL : Submodule.IsLattice D.host.E L) (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L)
      (hL' : Submodule.IsLattice D.host.E L') (hU' : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L')
      (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D (withLattice W L hL hU) P Q μ ↔ IsVolMeas D (withLattice W L' hL' hU') P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e → CarriesLattice W₁ W₂ e →
      ∃ Φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjugationBy (AF D.host.F) D.sp.cm.sig W₁.gram W₂.gram (frameMatrix W₁ W₂ e) Φ ∧
        (∀ h : HA (AF D.host.F) D.sp.cm.sig W₁.gram,
          HA.mat (AF D.host.F) D.sp.cm.sig W₁.gram h ∈ HFin (AF D.host.F) D.sp.cm.sig W₁.gram ↔
            HA.mat (AF D.host.F) D.sp.cm.sig W₂.gram (Φ h) ∈ HFin (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map Φ)) ∧
        ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram), IsVolMeas D W₁ P Q μ →
          ∀ 𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
              IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (Φ '' 𝓕) (μ.map Φ)

def VolumeInvariance (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D →
    ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
      (∃ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e) → D.vol W₁ = D.vol W₂

def VolumeIndependence (D : D7) : Prop :=
  LatticeIndependence D ∧ IsometryTransport D ∧ VolumeInvariance D

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
end
end

