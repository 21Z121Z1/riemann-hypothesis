import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

structure SFam (h k : ℕ) {o : Type} [CommRing o] (ζ : o) where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h k ζ s

  princ : univ.Principal

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre h k ζ s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} →
    c.Principal → ∃ f : S ⟶ X, f ≫ s = s' ∧ SiegPB c univ f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ X) (s' : Sp R ⟶ Sp o) (c : SiegPre h k ζ s'),
    x ≫ s = y ≫ s → SiegPB c univ x → SiegPB c univ y → x = y

def SRep {h p M : ℕ} (Ag : SiegelFamily h p M) : Prop :=
  IsSeparated Ag.s ∧ ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (ZP p M)) (c : SiegPre h M (zetaZP p M) s'), IsReduced S →
    Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Ag.X, f ≫ Ag.s = s' ∧ SiegPB c Ag.univ f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevUnder (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (t : TObj g k J b s) (τ : SAB H S)
    (lev : D.La → (𝟙_ (Over S) ⟶ τ.G)) : Prop :=
  ∃ φ : τ.G ≅ t.A, IsMonHom φ.hom ∧ LBIso τ.PP.L (t.L.pull φ.hom.left) ∧
    (∀ j, τ.act.act (a j) ≫ φ.hom = φ.hom ≫ t.act j) ∧ (∀ x y, lev (x + y) = lev x * lev y) ∧
    ∀ i, (lev (bas (Pi.single i 1)) ≫ φ.hom).left = (t.pt i).left

def TSieg {La : Type} [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La)
    (t : TObj g k J b s) {B : Type} [CommRing B] {ζ : B} {s' : S ⟶ Sp B} (c : SiegPre g k ζ s') : Prop :=
  letI := t.ab.comm
  ∃ φ : c.A ≅ t.A, IsMonHom φ.hom ∧ LBIso c.P ((abelian₂ t.A t.L).pull (φ.hom ⊗ₘ φ.hom).left) ∧
    ∀ i, (c.lev (bas'.symm (bas (Pi.single i 1))) ≫ φ.hom).left = (t.pt i).left

structure PELRep (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b s) :
    Prop where

  qproj : IsQProjOver s

  flat : Flat s

  red : IsReduced S

  rep : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (β : o →+* V) (t' : TObj g k J b (spMap β))
    (τ' : SAB H (Sp V)), Function.Injective β → IsPEL D a bas ρ t' τ' → ∃ f : Sp V ⟶ S, f ≫ s = spMap β ∧ TMap t' t f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ S) (s' : Sp R ⟶ Sp o) (t' : TObj g k J b s'),
    x ≫ s = y ≫ s → TMap t' t x → TMap t' t y → x = y

theorem isSeparated_of_isQProjOver {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) : IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsImmersion i := hi
  unfold PSpace.str
  infer_instance

theorem SFam.isSeparated {h : ℕ} {ζ : o} (F : SFam h k ζ) : IsSeparated F.s := isSeparated_of_isQProjOver F.qproj

theorem SFam.eq_constPt {h : ℕ} {ζ : o} (F : SFam h k ζ) (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ F.X)
    (c : SiegPre h k ζ (x ≫ F.s)) (hs : x ≫ F.s = constPt x ≫ F.s) (h₁ : SiegPB c F.univ x)
    (h₂ : SiegPB c F.univ (constPt x)) : x = constPt x := F.inj (DualNumber K) x (constPt x) (x ≫ F.s) c hs h₁ h₂

theorem SFam.sRep {h p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    SRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := ⟨F.isSeparated, fun S s' c hS hd hc => F.rep S s' c hS hd hc⟩

theorem PELRep.isSeparated {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o}
    {t : TObj g k J b s} (h : PELRep D a bas ρ t) : IsSeparated s := isSeparated_of_isQProjOver h.qproj

theorem LevUnder.lev_zero {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {t : TObj g k J b s}
    {τ : SAB H S} {lev : D.La → (𝟙_ (Over S) ⟶ τ.G)} (h : LevUnder D a bas t τ lev) : lev 0 = 1 := by
  obtain ⟨-, -, -, -, hadd, -⟩ := h
  have h0 : lev 0 * lev 0 = lev 0 * 1 := by rw [← hadd, add_zero, _root_.mul_one]
  exact _root_.mul_left_cancel h0

theorem LevUnder.lev_bas_pow {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {t : TObj g k J b s}
    {τ : SAB H S} {lev : D.La → (𝟙_ (Over S) ⟶ τ.G)} (h : LevUnder D a bas t τ lev) (i : Fin (2 * g)) :
    lev (bas (Pi.single i 1)) ^ k = 1 := by
  obtain ⟨φ, hφ, -, -, -, hpt⟩ := h
  haveI := hφ
  have e : lev (bas (Pi.single i 1)) ≫ φ.hom = t.pt i := Over.OverMorphism.ext (hpt i)
  apply (cancel_mono φ.hom).1
  rw [MonObj.pow_comp, e, t.torsion i, MonObj.one_comp]

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZM.DwModel

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

private lemma spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, spMap f = y :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

private lemma spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

theorem isGaloisCover_field (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisCover (L ≃ₐ[K] L) (fun σ => spMap (σ : L →+* L)) (spMap (algebraMap K L)) where
  finite := inferInstance
  one := by
    show Spec.map _ = _
    convert Spec.map_id (CommRingCat.of L)
    rfl
  mul a c := by
    show spMap (((a * c : L ≃ₐ[K] L) : L →+* L)) = _
    rw [← spMap_comp_moduli_spaces]
    rfl
  inv a := by
    rw [← spMap_comp_moduli_spaces]
    congr 1
    ext r
    exact a.commutes r
  fin := by
    show IsFinite (Spec.map _)
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  etale := by
    show Etale (Spec.map _)
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    show (algebraMap K L).Etale
    rw [RingHom.etale_algebraMap]
    exact ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  onto := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  fibre K' _ _ y y' h := by
    obtain ⟨f, rfl⟩ := spMap_surjective' y
    obtain ⟨f', rfl⟩ := spMap_surjective' y'
    rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
    have hfa := spMap_inj_lemma_3 h
    let _ : Algebra K K' := (f.comp (algebraMap K L)).toAlgebra
    let φ : L →ₐ[K] K' := { f with commutes' := fun _ => rfl }
    let φ' : L →ₐ[K] K' :=
      { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
    let Φ : (L ≃ₐ[K] L) → (L →ₐ[K] K') := fun a => φ.comp a.toAlgHom
    have hinj : Function.Injective Φ := by
      intro a b hab
      ext x
      exact f.injective (AlgHom.congr_fun hab x)
    have hcard : Nat.card (L →ₐ[K] K') ≤ Nat.card (L ≃ₐ[K] L) := by
      rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
    obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
    refine ⟨a, ?_, fun b hb => ?_⟩
    · show spMap f ≫ spMap (a : L →+* L) = spMap f'
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext x
      exact AlgHom.congr_fun ha x
    · have hb' : f.comp (b : L →+* L) = f' := by
        have hb0 : spMap f ≫ spMap (b : L →+* L) = spMap f' := hb
        rw [← spMap_comp_moduli_spaces] at hb0
        exact spMap_inj_lemma_3 hb0
      apply hinj
      ext x
      exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm

theorem isGaloisCover_complex :
    IsGaloisCover (ℂ ≃ₐ[ℝ] ℂ) (fun σ => spMap (σ : ℂ →+* ℂ)) (spMap (algebraMap ℝ ℂ)) ∧ Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
  have : IsAlgClosure ℝ ℂ := ⟨Complex.isAlgClosed, inferInstance⟩
  have : IsGalois ℝ ℂ := ⟨⟩
  exact ⟨isGaloisCover_field ℝ ℂ, by rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]⟩

theorem not_isGaloisCover_trivial :
    ¬ IsGaloisCover ℤˣ (fun _ => 𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) := by
  intro h
  obtain ⟨a, -, ha⟩ := h.fibre ℂ (𝟙 _) (𝟙 _) rfl
  have h1 : (1 : ℤˣ) = a := ha 1 (by simp)
  have h2 : (-1 : ℤˣ) = a := ha (-1) (by simp)
  exact absurd (h1.trans h2.symm) (by decide)

theorem dirMap_fst {K : Type} [Field K] {n : ℕ} (lam : (Fin n → K) →ₗ[K] K) (x : TrivSqZeroExt K (Fin n → K)) :
    (dirMap lam x).fst = x.fst ∧ (dirMap lam x).snd = lam x.snd := by
  constructor <;> simp [dirMap]

theorem densePrimes_univ_iff (R : Type) [CommRing R] : DenseP (Set.univ : Set (Ideal R)) ↔ _root_.IsReduced R := by
  constructor
  · intro h
    refine ⟨fun x hx => h x fun p _ hp => ?_⟩
    obtain ⟨k, hk⟩ := hx
    exact hp.mem_of_pow_mem k (hk ▸ p.zero_mem)
  · intro hR f hf
    have hnil : f ∈ nilradical R := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      exact fun p hp => hf p (Set.mem_univ p) hp
    exact (mem_nilradical.mp hnil).eq_zero

theorem not_denseP_two : ¬ DenseP ({Ideal.span {2}} : Set (Ideal ℤ)) := by
  intro h
  have h2 : (2 : ℤ) = 0 := h 2 fun p hp _ => by
    rw [Set.mem_singleton_iff.mp hp]
    exact Ideal.mem_span_singleton_self 2
  norm_num at h2

theorem odd_of_wfam {o : Type} [CommRing o] {g : ℕ} {J : Type} {n N' : ℕ} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (W : WFam n em C Mat κ) : Odd N' := by
  obtain ⟨x, ⟨-, hx⟩, -⟩ := W.Y.pts PUnit (algebraMap o PUnit) (fun _ => 0) (by
    unfold InMM
    exact ⟨fun _ _ => Subsingleton.elim _ _, fun q hq => absurd (Subsingleton.elim q ⊤) hq.ne_top⟩)
  let x' : Sp PUnit ⟶ W.U.toScheme := specPUnitIsInitial.to _
  have hx' : x' ≫ W.U.ι = x := specPUnitIsInitial.hom_ext _ _
  have h := (W.th PUnit x' (fun _ => 0)).2 (hx' ▸ hx)
  unfold TObj.HasTh Out.IsThetaPt at h
  exact h.1

end GlobalTheory.ZM.DwModel
end
end

