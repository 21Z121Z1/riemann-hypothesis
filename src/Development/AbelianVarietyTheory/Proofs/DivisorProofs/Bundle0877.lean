import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0860

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X Z T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem comb_pull (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (r : Z ⟶ X) (z : Z) (q : N.ι) (h : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) (r ≫ p) c z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp r p z ⊤ trivial, gs_comp r φ z _ h]

theorem Generates.pull {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hg : Generates a φ p c) (r : Z ⟶ X) : Generates a (r ≫ φ) (r ≫ p) c := by
  intro z q hz
  obtain ⟨j, hj⟩ := hg (r z) q hz
  exact ⟨j, by rw [comb_pull a φ p c r z q hz]; exact hj.map _⟩

theorem Proport.pull {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hp : Proport a b φ p Ψ c) (r : Z ⟶ X) :
    Proport a b (r ≫ φ) (r ≫ p) (r ≫ Ψ) c := by
  intro z q k hq hk j j'
  rw [comb_pull a φ p c r z q hq, comb_pull a φ p c r z q hq, gs_comp r Ψ z _ hk, gs_comp r Ψ z _ hk,
    ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem gs_top_comp {S : Scheme.{0}} (t : T ⟶ S) (z : T) (x : Γ(S, ⊤)) :
    (t.stalkMap z).hom (gs (𝟙 S) (t z) ⊤ x) = gs (𝟙 T) z ⊤ (t.appTop x) := by
  rw [← gs_comp t (𝟙 S) z ⊤ trivial, Category.comp_id]
  have e := gs_pull (𝟙 T) t z ⊤ trivial x
  rw [Category.id_comp] at e
  exact e.symm

theorem proport_zero {S : Scheme.{0}} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {eA : S ⟶ A₀} {eB : S ⟶ B₀}
    {uA : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ} {uB : ∀ z : S, H.ι → (S.presheaf.stalk z)ˣ}
    {α : Fin mA → Γ(S, ⊤)} {β : Fin mB → Γ(S, ⊤)} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (ha : ∀ i, IsVal eA uA (a i) (α i)) (hb : ∀ j, IsVal eB uB (b j) (β j)) (hn : Normal t c α β) :
    Proport a b (t ≫ eA) (𝟙 T) (t ≫ eB) c := by
  intro z q k hq hk j j'
  have hc : ∀ j, comb a (t ≫ eA) (𝟙 T) c z q j =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uA (t z) q).val := by
    intro j
    simp only [comb]
    have e : ∀ i, gs (t ≫ eA) z (N.U q) ((a i).f q) =
        gs (𝟙 T) z ⊤ (t.appTop (α i)) * (t.stalkMap z).hom (uA (t z) q).val := by
      intro i
      rw [gs_comp t eA z _ hq, ha i (t z) q hq, map_mul, gs_top_comp]
    simp only [e, hn j, gs_eq (𝟙 T) z ⊤ trivial, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
  have hbj : ∀ j, gs (t ≫ eB) z (H.U k) ((b j).f k) =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uB (t z) k).val := by
    intro j
    rw [gs_comp t eB z _ hk, hb j (t z) k hk, map_mul, gs_top_comp]
  rw [hc, hc, hbj, hbj]
  ring

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem snd_θ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : (snd (topS Rg) B).left ≫ θ B = 𝟙 _ := by
  have key : ∀ h : B ⟶ topS Rg, snd (topS Rg) B ≫ lift h (𝟙 B) = 𝟙 _ := by
    intro h
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply Over.OverMorphism.ext
      have : Mono (topS Rg).hom := by
        show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
      apply (cancel_mono (topS Rg).hom).1
      exact (Over.w _).trans (Over.w _).symm
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  rw [θ, ← Over.comp_left, key]
  rfl

theorem θ_comp_structure {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : θ B ≫ fA B = B.hom := by
  rw [θ]; exact Over.w _

end GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.hom_of_proport : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB T t A' B' _ _ φA' φB' Ψ c hH hvA hvB hA' hB' hΨ hgen hprop hnorm
  obtain ⟨hA, hB, hL, hM, -, -, -, hk, hva, -, hbB⟩ := hH
  have hA'ab : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hA'
  have hB'ab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'
  have hsnd : (snd (topS Rg) B).left ≫ B.hom = fA B := Over.w (snd (topS Rg) B)
  let Φl : A'.left ⟶ B'.left :=
    hB'.1.lift (Ψ ≫ (snd (topS Rg) B).left) A'.hom (by rw [Category.assoc, hsnd, hΨ])
  have hΦ1 : Φl ≫ φB' = Ψ ≫ (snd (topS Rg) B).left := hB'.1.lift_fst _ _ _
  have hΦ2 : Φl ≫ B'.hom = A'.hom := hB'.1.lift_snd _ _ _
  let Φ : A' ⟶ B' := Over.homMk Φl hΦ2
  have hΨΦ : Φ.left ≫ φB' ≫ θ B = Ψ := by
    show Φl ≫ φB' ≫ θ B = Ψ
    rw [← Category.assoc, hΦ1, Category.assoc, snd_θ, Category.comp_id]
  let e' : T ⟶ A'.left := η[A'].left
  have hEA : e' ≫ φA' = t ≫ eSec A := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hA'
  have hEB : (η[B'].left : T ⟶ B'.left) ≫ φB' = t ≫ eSec B := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hB'
  have hηA : e' ≫ A'.hom = 𝟙 T := Over.w η[A']
  have heB : eSec B ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hzero : e' ≫ Ψ = t ≫ eSec B ≫ θ B := by
    have hgen' := hgen.pull e'
    have hprop' := hprop.pull e'
    rw [← Category.assoc, hEA, hηA, Category.assoc] at hgen' hprop'
    refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ T T (fA B) (LPow A L k (topS Rg)) (LPow B M k (topS Rg)) mA mB bA bB _ (𝟙 T) c _ _
      (GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hB hM hk hva hbB) (LB.isLB_linComb hM _ _) (LB.isLB_linComb hL _ _) hgen' hprop'
      (proport_zero t c hvA hvB hnorm) ?_
    rw [Category.assoc, hΨ, ← Category.assoc, hηA, Category.id_comp, Category.assoc, Category.assoc, θ_comp_structure,
      heB]
    exact (Category.comp_id _).symm
  have hz : η[A'] ≫ Φ = η[B'] := by
    apply Over.OverMorphism.ext
    apply hB'.1.hom_ext
    · show e' ≫ Φl ≫ φB' = _
      rw [hΦ1, ← Category.assoc, hzero, hEB, Category.assoc, Category.assoc, θ_snd, Category.comp_id]
    · exact (Over.w _).trans (Over.w _).symm
  exact ⟨Φ, GlobalTheory.rigidity_holds T A' B' hA'ab hB'ab Φ hz, hΨΦ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilRat

theorem heisO_apply_zero {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem om_rat_actO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w := by
  intro D ψ hψ S T χS χT om H γ hγ γ' hγ' f hf w
  have h1 := H.om_heis γ γ' w f hf
  have h2 := H.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  rw [← heisO_apply_zero ψ (actO S T γ γ' w) (om (γ, γ') f), ← h1]
  exact h2.trans (heisO_apply_zero _ _ _)

end GlobalTheory.WeilRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFamilyConjConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ}

def unit (j : J) (p q : Fin (d j)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  Pi.single j (Matrix.single p q 1)

lemma pi_single_mul_ne {R : J → Type} [∀ i, MulZeroClass (R i)] {i j : J} (h : i ≠ j)
    (x : R i) (y : R j) : (Pi.single i x : Π k, R k) * Pi.single j y = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_apply, Ne.symm h]
  · simp [Pi.single_apply, hk]

lemma unit_mul_ne_factor {j j' : J} (h : j ≠ j') (p q : Fin (d j)) (p' q' : Fin (d j')) :
    unit (d := d) j p q * unit j' p' q' = 0 :=
  pi_single_mul_ne h _ _

lemma unit_mul_same (j : J) (p q r : Fin (d j)) :
    unit (d := d) j p q * unit j q r = unit j p r := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_same, _root_.mul_one]

lemma unit_mul_ne (j : J) (p q p' r : Fin (d j)) (h : q ≠ p') :
    unit (d := d) j p q * unit j p' r = 0 := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]

lemma pi_single_sum {R : J → Type} [∀ i, AddCommMonoid (R i)] {X : Type} (s : Finset X)
    (j : J) (f : X → R j) :
    (Pi.single j (∑ x ∈ s, f x) : Π k, R k) = ∑ x ∈ s, Pi.single j (f x) :=
  map_sum (AddMonoidHom.single R j) f s

lemma sum_unit_diag : ∑ j, ∑ k, unit (d := d) j k k = 1 := by
  simp only [unit]
  have : ∀ j, ∑ k, (Pi.single j (Matrix.single k k (1:ℂ)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      = Pi.single j 1 := by
    intro j
    rw [← Matrix.sum_single_one, pi_single_sum]
  simp only [this]
  exact Finset.univ_sum_single (fun j => (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))

lemma eq_sum_unit (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    t = ∑ j, ∑ p, ∑ q, t j p q • unit j p q := by
  conv_lhs => rw [← Finset.univ_sum_single t]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Matrix.matrix_eq_sum_single (t j)]
  simp only [unit, pi_single_sum, ← Pi.single_smul, Matrix.smul_single, smul_eq_mul, _root_.mul_one]

end HolConj

end GlobalTheory

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ} [∀ j, NeZero (d j)]
variable {A : Type} [Ring A] [Algebra ℂ A]

def conjMat (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) : A :=
  ∑ j, ∑ k, f (unit j k 0) * g (unit j 0 k)

lemma conjMat_self (f : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) :
    conjMat f f = 1 := by
  simp only [conjMat, ← map_mul, unit_mul_same, ← map_sum, sum_unit_diag, map_one]

lemma conjMat_unit (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (j' : J) (p q : Fin (d j')) :
    f (unit j' p q) * conjMat f g = conjMat f g * g (unit j' p q) := by
  have hL : f (unit j' p q) * conjMat f g = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single q]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ (Ne.symm hk), map_zero, zero_mul]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor (Ne.symm hj), map_zero, zero_mul]
    · simp
  have hR : conjMat f g * g (unit j' p q) = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single p]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ hk, map_zero, mul_zero]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor hj, map_zero, mul_zero]
    · simp
  rw [hL, hR]

lemma conjMat_intertwines (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    f t * conjMat f g = conjMat f g * g t := by
  rw [eq_sum_unit t]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    conjMat_unit]

end HolConj

theorem holFamily_conj_const : ∀ (S : Type) [Ring S] [Algebra ℂ S] [FiniteDimensional ℂ S] [IsSemisimpleRing S] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (S →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ)), IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * F b₀ a := by
  intro S _ _ _ _ g m B b₀ F hB hb₀ hF
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S
  let f : (Fin m → ℂ) →
      ((Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) :=
    fun b => (F b).comp e.symm.toAlgHom
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => HolConj.conjMat (f b) (f b₀)
  have hdiff : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := by
    intro i j
    simp only [h, f, HolConj.conjMat, Matrix.sum_apply, Matrix.mul_apply, AlgHom.comp_apply]
    refine DifferentiableOn.fun_sum fun _ _ => DifferentiableOn.fun_sum fun _ _ =>
      DifferentiableOn.fun_sum fun _ _ => (hF _ _ _).mul_const _
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hdiff i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hc
  have h₀ : h b₀ = 1 := HolConj.conjMat_self _
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h₀]⟩,
    Set.inter_subset_left, h₀, fun i j => (hdiff i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  have := HolConj.conjMat_intertwines (f b) (f b₀) (e a)
  simpa [f] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTestsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homFixedPullbackRep_of_affineTests : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | exact @GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | exact GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | (intros; apply GlobalTheory.EndLoc.HomFixGlue.rep_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIndepRangeInc
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.SumSlope

variable {K : Type} [Field K] [NumberField K] {O : Type} [Fintype O] [DecidableEq O] {ι : O → Type}
  [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)]

def sumNorm (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (σ : K →+* ℂ) (x : ∀ o, ι o → K) : ℝ :=
  Real.sqrt (∑ o, matNorm (Y o) σ (x o) ^ 2)

abbrev inc (o : O) : (ι o → K) →ₗ[K] (∀ o, ι o → K) := LinearMap.single K (fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem inc_injective (o : O) : Function.Injective (inc (K := K) (ι := ι) o) :=
  Pi.single_injective (M := fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem iSupIndep_range_inc : iSupIndep fun o => LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
  have h : (⨆ p, ⨆ (_ : p ≠ o), LinearMap.range (inc (K := K) (ι := ι) p)) ≤
      LinearMap.ker (LinearMap.proj (R := K) (φ := fun o => ι o → K) o) := by
    refine iSup₂_le fun p hp => ?_
    rintro _ ⟨x, rfl⟩
    simp [Pi.single_eq_of_ne hp.symm]
  refine Submodule.disjoint_def.2 ?_
  rintro _ ⟨x, rfl⟩ hx
  have h1 : x = 0 := by simpa using h hx
  rw [h1, map_zero]

variable (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ)

omit [NumberField K] [Fintype O] [DecidableEq O] [∀ o, DecidableEq (ι o)] in
theorem matNorm_zero (o : O) (σ : K →+* ℂ) : matNorm (Y o) σ 0 = 0 := by
  have h : (fun j : ι o => σ ((0 : ι o → K) j)) = 0 := by funext j; simp
  simp only [matNorm, h, Matrix.mulVec_zero]
  simp

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_inc (o : O) (σ : K →+* ℂ) (x : ι o → K) : sumNorm Y σ (inc o x) = matNorm (Y o) σ x := by
  unfold sumNorm
  rw [Finset.sum_eq_single o]
  · simp only [LinearMap.coe_single, Pi.single_eq_same]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  · intro p _ hp
    simp only [LinearMap.coe_single, Pi.single_eq_of_ne hp, matNorm_zero]
    simp
  · intro h; exact absurd (Finset.mem_univ o) h

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_sum (σ : K →+* ℂ) (f : O → ∀ o, ι o → K) (hf : ∀ o, f o ∈ LinearMap.range (inc (K := K) (ι := ι) o)) :
    sumNorm Y σ (∑ o, f o) ^ 2 = ∑ o, sumNorm Y σ (f o) ^ 2 := by
  choose g hg using hf
  have h : ∑ o, f o = g := by
    rw [← Finset.univ_sum_single g]
    exact Finset.sum_congr rfl fun o _ => (hg o).symm
  rw [h, sumNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun o _ => by rw [← hg o, sumNorm_inc]

theorem hasGram_sumNorm (hY : ∀ o σ, (Y o σ).det ≠ 0) : HasGram (sumNorm Y) := by
  refine GlobalTheory.OrthSumGram.orth_sum_hasGram K _ O (sumNorm Y) (fun o => LinearMap.range (inc (K := K) (ι := ι) o))
    (fun _ _ => Real.sqrt_nonneg _) iSupIndep_range_inc (LinearMap.iSup_range_single K _) (fun o => ?_)
    (fun σ f => sumNorm_sum Y σ (fun o => f o) fun o => (f o).2)
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := (isGram_matNorm K (ι o) (Y o) (hY o)).2
  let e := LinearEquiv.ofInjective (inc (K := K) (ι := ι) o) (inc_injective o)
  have h := GlobalTheory.RestrictNorm.hasGram_comp (matNorm (Y o)) e.symm.toLinearMap e.symm.injective b X hG
  convert h using 3 with σ x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact sumNorm_inc Y o σ y

theorem le_slope_sq_of_sum : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (O : Type) [Fintype O] [Nonempty O] (ι : O → Type) [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] [∀ o, Nonempty (ι o)] (Nv : (K →+* ℂ) → V → ℝ) (M : Submodule (𝓞 K) V) (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (L : ∀ o, Submodule (𝓞 K) (ι o → K)) (Φ : (∀ o, ι o → K) →ₗ[K] V) (s : ℝ), HasGram Nv → M.FG → (∀ o σ, (Y o σ).det ≠ 0) → (∀ o, Submodule.IsLattice K (L o)) → Function.Injective Φ → (∀ x, (∀ o, x o ∈ L o) → Φ x ∈ M) → (∀ v ∈ M, v ∈ LinearMap.range Φ) → (∀ σ x, Nv σ (Φ x) ^ 2 ≤ ∑ o, matNorm (Y o) σ (x o) ^ 2) → (∀ o, s ≤ slope_sq (matNorm (Y o)) (L o)) → s ≤ slope_sq Nv M := by
  intro K _ _ _ V _ _ _ _ O _ _ ι _ _ _ Nv M Y L Φ s hNv hM hY hL hΦ hin hrg hle hs
  classical
  have hG := hasGram_sumNorm Y hY
  let P : O → Submodule (𝓞 K) (∀ o, ι o → K) := fun o => (L o).map ((inc o).restrictScalars (𝓞 K))
  have hsp : ∀ o, Submodule.span K (P o : Set (∀ o, ι o → K)) = LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
    rw [LinearMap.range_eq_map, ← (hL o).span_eq_top, ← Submodule.span_image]
    rfl
  have hP : ∀ o, (P o).FG := fun o => (hL o).fg.map _
  obtain ⟨hrk, hdeg⟩ := GlobalTheory.OrthRankDeg.rkK_deg_iSup K _ O (sumNorm Y) P hG hP
    fun σ f hf => sumNorm_sum Y σ f fun o => hsp o ▸ hf o
  have hd : ∀ o, (Formalism.HN.rkK (P o) : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (P o) := fun o => by
    obtain ⟨h1, h2⟩ := (GlobalTheory.RestrictNorm.restrict_deg K _ _ (sumNorm Y) (inc o) (inc_injective o) hG).2
      (L o) (hL o).fg
    have h3 : (fun σ x => sumNorm Y σ (inc o x)) = matNorm (Y o) := by
      funext σ x; exact sumNorm_inc Y o σ x
    rw [h3] at h2
    show (Formalism.HN.rkK ((L o).map _) : ℝ) * _ ≤ GlobalTheory.AllWt.deg _ ((L o).map _)
    rw [h1, h2, GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope]
    exact mul_le_mul_of_nonneg_left (by linarith [hs o]) (Nat.cast_nonneg _)
  have htop : Submodule.span K ((⨆ o, P o : Submodule (𝓞 K) _) : Set (∀ o, ι o → K)) = ⊤ := by
    rw [eq_top_iff, ← LinearMap.iSup_range_single K (fun o => ι o → K)]
    refine iSup_le fun o => ?_
    rw [← hsp o]
    exact Submodule.span_mono (le_iSup P o)
  have hmap : (⨆ o, P o).map (Φ.restrictScalars (𝓞 K)) ≤ M := by
    rw [Submodule.map_iSup]
    refine iSup_le fun o => ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine hin _ fun p => ?_
    by_cases hp : p = o
    · subst hp; simpa using hx
    · simp [Pi.single_eq_of_ne hp]
  have hspM : Submodule.span K (M : Set V) = LinearMap.range Φ := by
    refine le_antisymm (Submodule.span_le.2 hrg) ?_
    rw [LinearMap.range_eq_map, ← htop, ← Submodule.span_image]
    exact Submodule.span_mono hmap
  have hrkS : Formalism.HN.rkK (⨆ o, P o) = finrank K (∀ o, ι o → K) := by
    rw [Formalism.HN.rkK, htop, finrank_top]
  have hrkM : Formalism.HN.rkK M = Formalism.HN.rkK (⨆ o, P o) := by
    rw [hrkS, Formalism.HN.rkK, hspM, LinearMap.finrank_range_of_inj hΦ]
  have key := GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le K _ V (sumNorm Y) Nv Φ (fun _ => 1) (⨆ o, P o) M ⊤ hG hNv hΦ
    (fun _ => one_pos) (fun _ => rfl)
    (fun σ x => by rw [one_mul]; exact (le_abs_self _).trans (Real.abs_le_sqrt (hle σ x)))
    (Submodule.fg_iSup _ hP) hM top_ne_bot (by rwa [Submodule.top_smul]) hrkM
  have hpos : (0 : ℝ) < Formalism.HN.rkK M := by
    rw [hrkM, hrkS]
    exact_mod_cast Module.finrank_pos
  have h1 : (Formalism.HN.rkK M : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (⨆ o, P o) := by
    rw [hdeg, hrkM, hrk, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun o _ => hd o
  simp only [Real.log_one, Finset.sum_const_zero, Ideal.absNorm_top, Nat.cast_one, zero_div, neg_zero, sub_zero,
    mul_zero, add_zero] at key
  have h2 := h1.trans key
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope] at h2
  have h3 := le_of_mul_le_mul_left h2 hpos
  linarith

end GlobalTheory.SumSlope

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmpleStatement
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  first | exact @GlobalTheory.AmpleTwistLB.ample_pow_div | exact GlobalTheory.AmpleTwistLB.ample_pow_div | (intros; apply GlobalTheory.AmpleTwistLB.ample_pow_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVectorStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramFrame_embeddingMatrixNormOfVector : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  first | exact @GlobalTheory.DefPt.isGram_matNorm | exact GlobalTheory.DefPt.isGram_matNorm | (intros; apply GlobalTheory.DefPt.isGram_matNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamilyStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K), IsAdelic A → Submodule.IsLattice K (locLat A) := by
  first | exact @GlobalTheory.LocMatLat.isLattice_locLat | exact GlobalTheory.LocMatLat.isLattice_locLat | (intros; apply GlobalTheory.LocMatLat.isLattice_locLat <;> assumption)
end

