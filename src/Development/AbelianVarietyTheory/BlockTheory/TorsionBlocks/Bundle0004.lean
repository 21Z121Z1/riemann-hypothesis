import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BlockRootsCuspidal
section
open Polynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockRootsCuspidal

def IsBlockRoots {F : Type} [Monoid F] (g : ℕ) (B : Multiset (ℕ × ℕ)) (Rt : Multiset F) : Prop :=
  ∃ M : Multiset ((ℕ × ℕ) × Multiset F),
    M.map Prod.fst = B ∧
    (∀ p ∈ M, Multiset.card p.2 = p.1.1 ∧ p.2.map (fun x => x ^ g) = p.2) ∧
    (M.map fun p => p.1.2 • p.2).sum = Rt

def labelRoots (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) :
    Multiset (Formalism.BasicNotions.Fb (D.host.g k) (D.host.g_prime k)) :=
  @Formalism.CyclotomicNorms.rootsBar (D.host.g k) ⟨D.host.g_prime k⟩ (D.nd.lab k σ v)

def BlockRootsAt (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  IsBlockRoots (D.host.g k) (D.ntypes.bc σ) (labelRoots D σ k v)

def TameAt (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (lam : D.what₂.places.Pl) : Prop :=
  Matrix.charpoly
      ((D.ntypes.rbar σ lam (D.ntypes.tg k v) :
          GL (Fin D.R.r) (Formalism.BasicNotions.Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam))) :
        Matrix (Fin D.R.r) (Fin D.R.r)
          (Formalism.BasicNotions.Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam))) =
    ((labelRoots D σ k v).map fun x =>
      X - C (D.ntypes.iota k v lam (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar lam) x))).prod ∧
  ∃ φ : Formalism.MainNotions.N.GE D.nd,
    D.ntypes.rbar σ lam (φ * D.ntypes.tg k v * φ⁻¹) =
      D.ntypes.rbar σ lam (D.ntypes.tg k v) ^ D.host.g k

def LabelsAndTameInertia (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ σ : D.what₂.FT, D.nd.goodRow σ → ∀ (k : Fin 2) (v : D.nd.PlG k),
    BlockRootsAt D σ k v ∧
    (D.ntypes.cuspidal σ → ∀ lam : D.what₂.places.Pl, D.what₂.places.resChar lam ≠ D.host.g k →
      TameAt D σ k v lam)

theorem IsBlockRoots.le_one {F : Type} [Monoid F] {g : ℕ} {B : Multiset (ℕ × ℕ)} {Rt : Multiset F}
    (h : IsBlockRoots g B Rt) (hR : Rt.Nodup) : ∀ p ∈ B, 0 < p.1 → p.2 ≤ 1 := by
  classical
  obtain ⟨M, rfl, hM, rfl⟩ := h
  intro p hp h0
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
  have hc := (hM q hq).1
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (hc ▸ h0)
  have hle : q.1.2 • q.2 ≤ (M.map fun p => p.1.2 • p.2).sum :=
    Multiset.single_le_sum (fun _ _ => Multiset.zero_le _) _ (Multiset.mem_map_of_mem _ hq)
  have h1 := Multiset.count_le_of_le x hle
  have h2 := Multiset.nodup_iff_count_le_one.1 hR x
  rw [Multiset.count_nsmul] at h1
  have h3 := Multiset.one_le_count_iff_mem.2 hx
  nlinarith

theorem blockRootsAt_of_cuspidal (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k)
    (h : D.ntypes.cuspidal σ) : BlockRootsAt D σ k v := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hdeg : ((D.nd.lab k σ v).map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))).natDegree
      = D.R.r := by
    rw [natDegree_map]; exact (D.nd.lab_monic k σ v).2
  have hcard := IsAlgClosed.card_roots_eq_natDegree
    (p := (D.nd.lab k σ v).map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))))
  refine ⟨{((D.R.r, 1), labelRoots D σ k v)}, ?_, ?_, ?_⟩
  · rw [Multiset.map_singleton]; exact h.symm
  · intro p hp
    rw [Multiset.mem_singleton] at hp
    subst hp
    refine ⟨hcard.trans hdeg, ?_⟩
    have := roots_map_of_injective_of_card_eq_natDegree
      (f := frobenius (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.host.g k)) (RingHom.injective _) hcard
    rw [Polynomial.map_map, RingHom.ext_zmod ((frobenius _ _).comp _)
      (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))] at this
    exact this
  · simp

end GlobalTheory.IndefiniteRowSideFullHecke.BlockRootsCuspidal
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CongruenceMaxGalois
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

def CongrMax {l : ℕ} [Fact l.Prime] (a b : Qbar l) : Prop := ‖a - b‖ < 1

def IsReduction {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l a : ℕ} [Fact l.Prime]
    (r : Γ →* GL (Fin a) (Qbar l)) (rb : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsSSRep rb ∧ IsOpen (rb.ker : Set Γ) ∧
    ∃ red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l, ∀ g : Γ, ∃ p : (Zbar l)[X],
      p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
      p.map red = ((rb g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) :
        Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω) (u : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → B.valuation (u y / y - 1) < 1

def UnramOver {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (L : IntermediateField E Ω) (g : ℕ) : Prop :=
  ∀ w ∈ placesOver E g, ∀ B : ValuationSubring Ω, IsPlaceOver (F := E) B w →
    Ine (F := E) B ≤ L.fixingSubgroup

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (φ : GalE D),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) φ →
    ((r φ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def IsTameLift (k : Fin 2) (v : D.nd.PlG k) (t : GalE D) : Prop :=
  ∃ h u : GalE D, IsWildAt (D.nd.plOm.1 (D.naut.plGw k v)) u ∧
    (t = h * (D.ntypes.tg k v * u) * h⁻¹ ∨
      ∃ c : D.nd.Om ≃+* D.nd.Om, IsCMConjOm D.host.E D.nd.Om c ∧
        ∀ x, t x = c ((h * (D.ntypes.tg k v * u) * h⁻¹) (c.symm x)))

def bracket (k : Fin 2) (x : (ZMod (D.host.g k))ˣ) : ℂ :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (x : ZMod (D.host.g k)))

def IsRowAt (j : ℕ) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot j σ ≠ ⊥ ∨ σ ∈ Set.range D.what₂.ft ∨ σ ∈ Set.range D.what₂.ft0

def IsCuspBaseChange (i : D.nd.Loc) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  D.naut.csd π ∧ D.naut.ralg π ∧
    ∀ w, IsSplitPl D.host w → D.naut.locG π w = D.naut.locW i σ w

def ResidIrred (l : ℕ) [Fact l.Prime] (rb : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  Formalism.CyclotomicNorms.IrredOn rb ⊤ ∧
  ∀ (L : IntermediateField D.host.E D.nd.Om), FiniteDimensional D.host.E L → IsGalois D.host.E L →
    IsSolvable (L ≃ₐ[D.host.E] L) →
    ∀ k : Fin 2, l ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) → UnramOver L (D.host.g k) →
      Formalism.CyclotomicNorms.IrredOn rb L.fixingSubgroup

def TameAvoids (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : GalE D →* GL (Fin D.R.r) (Qbar l)) : Prop :=
  ∀ k : Fin 2, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) (t : GalE D), IsTameLift D k v t →
    ∀ (j : Fin D.R.m) (α : Qbar l),
      ((r t : GL (Fin D.R.r) (Qbar l)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar l)).charpoly.IsRoot α →
      ¬ CongrMax α (ι.symm (bracket D k (D.nd.chiT k v j))) ∧
      ¬ CongrMax α (ι.symm (bracket D k (D.nd.chiT k v j)⁻¹))

def GoodRowIrreducibility : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), IsRowAt D (D.nd.j i) σ → D.nd.goodRow σ →
    ∃ π : D.naut.CG D.R.r, IsCuspBaseChange D i σ π ∧
      ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
        (∃ r rb, IsGaloisRepOf D π l ι r ∧ IsReduction r rb) ∧
        ∀ r, IsGaloisRepOf D π l ι r →
          (∀ rb, IsReduction r rb → ResidIrred D l rb) ∧ TameAvoids D l ι r

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FactorSeriesSupport
section
noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

open Formalism.BasicNotions

def IsLabel (N : ℕ) {g : ℕ} (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0

def rootExp (N g : ℕ) : ℕ := (Finset.Icc 1 N).lcm fun d => g ^ d - 1

def IsPowLabel {g : ℕ} [Fact g.Prime] (a : ℤ) (f f' : (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map fun x => x ^ a

def atFactor {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (i : ι) :
    MonoidAlgebra ℂ (G i) →ₐ[ℂ] MonoidAlgebra ℂ (∀ i, G i) :=
  open Classical in MonoidAlgebra.mapDomainAlgHom ℂ ℂ (MonoidHom.mulSingle G i)

open Classical in
theorem atFactor_single {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (i : ι) (γ : G i) (c : ℂ) :
    atFactor i (MonoidAlgebra.single γ c) = MonoidAlgebra.single (Pi.mulSingle i γ) c := by
  simp [atFactor]

theorem atFactor_central {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (i : ι)
    (z : MonoidAlgebra ℂ (G i)) (hz : ∀ b, z * b = b * z) :
    atFactor i z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i)) := by
  classical
  rw [Subalgebra.mem_center_iff]
  have key : ∀ (δ : ∀ i, G i), δ i = 1 → ∀ y : MonoidAlgebra ℂ (G i),
      MonoidAlgebra.single δ (1 : ℂ) * atFactor i y = atFactor i y * MonoidAlgebra.single δ 1 := by
    intro δ hδ y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | single γ c =>
      rw [atFactor_single, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
        one_mul, mul_one]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [hδ]
      · simp [Pi.mulSingle_eq_of_ne hj]
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  | single γ c =>
    have h1 : MonoidAlgebra.single γ c =
        MonoidAlgebra.single (Function.update γ i 1) (1 : ℂ) *
          atFactor i (MonoidAlgebra.single (γ i) c) := by
      rw [atFactor_single, MonoidAlgebra.single_mul_single, one_mul]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
    rw [h1, mul_assoc, ← map_mul, ← hz, map_mul, ← mul_assoc,
      key _ (Function.update_self _ _ _), mul_assoc]

variable (D : D7)

def serAt (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
  ⟨atFactor (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      ⟨k, v⟩ (D.ntypes.eSer k f),
    atFactor_central _ _ (D.ntypes.eSer_central k f)⟩

def GaloisAction : Prop :=
  ∀ (k : Fin 2) (α : ℂ ≃+* ℂ) (a : ℤ),
    (∀ ζ : ℂ, ζ ^ rootExp D.R.r (D.host.g k) = 1 → α ζ = ζ ^ a) →
    ∀ f : (ZMod (D.host.g k))[X], IsLabel D.R.r f →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ f' : (ZMod (D.host.g k))[X], IsLabel D.R.r f' ∧ IsPowLabel a f f' ∧
        ∀ γ : GL (Fin D.R.r) (ZMod (D.host.g k)),
          α ((D.ntypes.eSer k f).coeff γ) = (D.ntypes.eSer k f').coeff γ

def SupportOneBlock : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
    ∀ (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
      IsLabel D.R.r f → f ≠ D.ntypes.labPar k σ' v →
      ∀ x ∈ D.ntypes.MtPar μ j σ', D.ntypes.cenMt μ j (serAt D k v f) x = 0

def SupportAllBlocks : Prop :=
  ∀ (μ : D.what₂.Tup) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k)
    (f : (ZMod (D.host.g k))[X]), IsLabel D.R.r f →
      (haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
       ¬ IsPowLabel (-1) (D.ntypes.labPar k σ' v) f) →
      ∀ x ∈ D.ntypes.AmbPar μ σ', D.ntypes.cenAmb μ (serAt D k v f) x = 0

def SeriesLocal : Prop := GaloisAction D ∧ SupportOneBlock D ∧ SupportAllBlocks D

example {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : IsPowLabel 1 f f := by
  simp [IsPowLabel]

theorem IsPowLabel.unique {g : ℕ} [Fact g.Prime] {a : ℤ} {f f₁ f₂ : (ZMod g)[X]}
    (h₁ : IsPowLabel a f f₁) (h₂ : IsPowLabel a f f₂) (m₁ : f₁.Monic) (m₂ : f₂.Monic) : f₁ = f₂ := by
  have h : Formalism.CyclotomicNorms.rootsBar f₁ = Formalism.CyclotomicNorms.rootsBar f₂ := h₁.trans h₂.symm
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  have e : ∀ p : (ZMod g)[X], p.Monic → p.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) =
      ((Formalism.CyclotomicNorms.rootsBar p).map fun x => X - C x).prod := fun p hp =>
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      (IsAlgClosed.card_roots_eq_natDegree)).symm
  rw [e f₁ m₁, e f₂ m₂, h]

theorem rootExp_ne_zero (N g : ℕ) (hg : 2 ≤ g) : rootExp N g ≠ 0 := by
  unfold rootExp
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨d, hd, h⟩
  have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.1 hd).1; omega
  have : 1 < g ^ d := Nat.one_lt_pow hd1 (by omega)
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.OddWindowBounds
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OddWindowBounds

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions ReciprocityTheory.Gal

def eFactor {L : Type} [Field L] (q : ℕ) (s : ℤ) (Y : Lˣ) : L :=
  (1 - (Y : L) * (q : L) ^ (-s)) * (1 - ((Y⁻¹ : Lˣ) : L) * (q : L) ^ (-s)) +
    ((q : L) - 1) * (q : L) ^ (-(2 * s))

example : eFactor (L := ℚ) 3 1 1 = 2 / 3 := by
  norm_num [eFactor]

def bigN (R : Ranks) : ℕ := R.k + R.m * (R.t + (R.r + 6) + 1)

def UnramAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A' : Type} [Group A']
    (φ : G E Ω →* A') (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (X : NTw R H what₂ LL0 N)

def Admissible (i : X.Tw) (lam : X.abelian₂ i) (Q : Finset (PlE H)) : Prop :=
  ∀ P ∈ Q, IsSplitPl H P ∧ (∀ P', IsConjPl H P P' → P' ∈ Q) ∧
    P ∉ placesOver H.E (X.l i) ∧ UnramAt (X.lamG i lam) P

def evalTh (i : X.Tw) (lam : X.abelian₂ i) (Q : Finset (PlE H)) {L : Type} [Field L]
    (φ : FractionRing (X.O i) →+* L) (ψ : X.RCG i Q →* Lˣ) : L :=
  ∑ x : X.RCG i Q, φ (X.th i Q lam x) * (ψ x : L)

def lamPsi (i : X.Tw) (lam : X.abelian₂ i) (Q : Finset (PlE H)) {L : Type} [Field L]
    (φ : FractionRing (X.O i) →+* L) (ψ : X.RCG i Q →* Lˣ) : G H.E N.Om →* Lˣ :=
  ((Units.map (φ.comp (algebraMap (X.O i) (FractionRing (X.O i)))).toMonoidHom).comp
    (X.lamG i lam)) * ψ.comp (X.art i Q)

open Classical in

def RelAt (i : X.Tw) (lam : X.abelian₂ i) (s : ℤ) : Prop :=
  ∀ Q : Finset (PlE H), Admissible X i lam Q →
  ∀ P ∈ Q, ∀ P' : PlE H, IsConjPl H P P' →
  ∀ (L : Type) [Field L] (φ : FractionRing (X.O i) →+* L) (ψ : X.RCG i Q →* Lˣ),
    UnramAt (ψ.comp (X.art i Q)) P → UnramAt (ψ.comp (X.art i Q)) P' →
    ∃ ψ' : X.RCG i (Q \ {P, P'}) →* Lˣ,
      ψ'.comp (X.res i Q (Q \ {P, P'}) Finset.sdiff_subset) = ψ ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
      ∀ σ : G H.E N.Om, IsFrob (F := H.E) A (normV P) σ →
        evalTh X i lam Q φ ψ =
          eFactor (normV P) s (lamPsi X i lam Q φ ψ σ⁻¹) * evalTh X i lam (Q \ {P, P'}) φ ψ'

def DistRel : Prop :=
  ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ s : ℤ, X.s2 i lam = 2 * s ∧ 1 ≤ s ∧ s ≤ (bigN R : ℤ) + 1 ∧
    RelAt X i lam s

end Record

def ToricDistribution (D : D7) : Prop := DistRel D.ntw

end GlobalTheory.IndefiniteRowSideFullHecke.OddWindowBounds

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ReductionClauses
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReductionClauses

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Clauses

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def DepthZero {w : PlE H} (L : A.LP w) : Prop :=
  ∀ σ ∈ wildSet N (N.plOm.1 w), A.inePol L σ = (X - 1) ^ A.lpDim L

def Hyp (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)) : Prop :=
  ((∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r) ∧
  HasParamX N A i x Sig ∧
  (∀ k, ∀ w ∈ placesOver H.E (H.g k), DepthZero N A (isoLoc N A Sig w)) ∧
  goodSig N A Sig

def ClauseA (Sig : List (Part A.CG)) : Prop :=
  ∃ π : A.CG R.r, Sig = [⟨R.r, π, 1⟩] ∧ A.csd π ∧ A.ralg π

def redBar (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    G H.E N.Om →* GL (Fin R.r) (Formalism.CyclotomicNorms.Fbar (N.l i)) :=
  mapRep ((A.kFbar i).comp (IsLocalRing.residue (N.O i))) ρ

def ClauseB (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Formalism.CyclotomicNorms.IrredOn (redBar N A i ρ) ⊤

def ClauseC (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ L : IntermediateField H.E N.Om, FiniteDimensional H.E L → IsGalois H.E L →
    Group.IsSolvable (L ≃ₐ[H.E] L) →
    ∀ k : Fin 2, N.l i ∉ Formalism.CyclotomicNorms.BB R.r (H.g k) →
      (∀ w ∈ placesOver H.E (H.g k), ∀ B : ValuationSubring N.Om, IsPlaceOver (F := H.E) B w →
        Ine (F := H.E) B ≤ L.fixingSubgroup) →
      Formalism.CyclotomicNorms.IrredOn (redBar N A i ρ) L.fixingSubgroup

variable {A} in

def rootQ (T : NTypes A) (i : N.Loc) (k : Fin 2) (u : (ZMod (H.g k))ˣ) : Qbar (N.l i) :=
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  (A.iotaQC i).symm (T.teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k)) (u : ZMod (H.g k))))

def NoEigCongr (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (γ : G H.E N.Om)
    (z : Qbar (N.l i)) : Prop :=
  ∀ α : Qbar (N.l i),
    ((mapRep (iotaOQ N A i) ρ γ : GL (Fin R.r) (Qbar (N.l i))) :
      Matrix (Fin R.r) (Fin R.r) (Qbar (N.l i))).charpoly.IsRoot α → ¬ ‖α - z‖ < 1

variable {A} in

def ClauseD (T : NTypes A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ (v : N.PlG k) (γ : G H.E N.Om),
    (γ = T.tg k v ∨ ∃ c : N.Om ≃+* N.Om, IsCMConjOm H.E N.Om c ∧
      ∀ y, γ y = c (T.tg k v (c.symm y))) →
    ∀ j' : Fin R.m,
      NoEigCongr N A i ρ γ (rootQ N T i k (N.chiT k v j')) ∧
      NoEigCongr N A i ρ γ (rootQ N T i k (N.chiT k v j')⁻¹)

def ClauseTame (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ w ∈ placesOver H.E (H.g k), ∀ B : ValuationSubring N.Om,
    IsPlaceOver (F := H.E) B w → ∀ γ : G H.E N.Om, TameGenAt B γ →
      ¬ ((redRep N i ρ γ : GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
          Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))).charpoly.IsRoot
        (IsLocalRing.residue (N.O i) ((N.chi i 1 γ : (N.O i)ˣ) : N.O i)) ∧
      ¬ ((redRep N i ρ γ : GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
          Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))).charpoly.IsRoot
        (IsLocalRing.residue (N.O i) (((N.chi i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i))

variable {A} in

def RepClauses (T : NTypes A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ClauseB N A i ρ ∧ ClauseC N A i ρ ∧ ClauseD N T i ρ ∧ ClauseTame N i ρ

theorem ClauseA.cusp {Sig : List (Part A.CG)} (h : ClauseA N A Sig) : IsCuspIso N A Sig :=
  let ⟨π, h1, _⟩ := h; ⟨π, h1⟩

end Clauses

def PointIrreducibility (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), Hyp D.nd D.naut i x Sig →
    ClauseA D.nd D.naut Sig ∧
    ∀ (i' : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i')),
      IsRepOfSig D.nd D.naut i' Sig ρ → RepClauses D.nd D.ntypes i' ρ

end GlobalTheory.IndefiniteRowSideFullHecke.ReductionClauses

end
end

