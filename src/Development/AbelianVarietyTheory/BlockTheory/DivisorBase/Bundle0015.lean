import Mathlib
import Formalism.CyclotomicNorms.Bundle0002
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

section OnePrime

variable {g : ℕ} [Fact g.Prime]

def rootC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def labelChar (ω : Fbar g →*₀ ℂ) (d : ℕ) (x y : Fbar g) : ℂ :=
  ω x ^ sInf {a : ℕ | ω y = rootC (g ^ d - 1) ^ a}

open Classical in

def cuspVal (ω : Fbar g →*₀ ℂ) (x : Fbar g) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) : ℂ :=
  if ∃ (p : (ZMod g)[X]) (k : ℕ), Irreducible p ∧ M.charpoly = p ^ k then
    (-1) ^ (Fintype.card ι - 1) *
      ∑ y ∈ (rootsBar M.charpoly).toFinset, labelChar ω (Fintype.card ι) x y *
        ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) y)),
          (1 - (g : ℂ) ^ ((rootsBar M.charpoly).toFinset.card * i))
  else 0

def IsTypeChar (ω : Fbar g →*₀ ℂ) {r : ℕ} (f : (ZMod g)[X]) (χ : GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (φ : ℕ → (ZMod g)[X]) (x : ℕ → Fbar g) (n : ℕ)
    (ρ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)),
    (∀ c ∈ Finset.univ.image b, (φ c).Monic ∧ Irreducible (φ c) ∧
      (φ c).natDegree = Fintype.card {a : Fin r // b a = c} ∧ x c ∈ rootsBar (φ c)) ∧
    f = ∏ c ∈ Finset.univ.image b, φ c ∧
    IsCuspDatum b ρ ∧
    (∀ p, ρ.character p = ∏ c ∈ Finset.univ.image b, cuspVal ω (x c) (blkMat b c p)) ∧
    ∀ y, χ y = (parInd b ρ).character y

def IsTameLabel (ω : Fbar g →*₀ ℂ) (η : (ZMod g)ˣ → ℂ) (c : (ZMod g)ˣ) : Prop :=
  ∀ z : (ZMod g)ˣ, η z =
    labelChar ω 1 (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) (algebraMap (ZMod g) (Fbar g) (z : ZMod g))

theorem labelChar_one_right (ω : Fbar g →*₀ ℂ) (d : ℕ) (x : Fbar g) : labelChar ω d x 1 = 1 := by
  have : sInf {a : ℕ | ω 1 = rootC (g ^ d - 1) ^ a} = 0 := by
    rw [Nat.sInf_eq_zero]; left; simp
  rw [labelChar, this, pow_zero]

example (ω : Fbar g →*₀ ℂ) : IsTameLabel ω (fun _ => 1) 1 := by
  intro z; simp [labelChar]

end OnePrime

section BothPrimes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}

theorem pb_ne_zero (hT : IsTypeDatum gp pb) (i : Fin 2) : pb i ≠ 0 := by
  intro h
  have h1 := hT.norm i
  rw [h] at h1
  have h2 : (gp i : E) = 0 := by rw [← h1]; simp
  exact (hT.prime i).ne_zero (by exact_mod_cast h2)

def toBoth (hT : IsTypeDatum gp pb) (i : Fin 2) (v : ↥(primesOf (pb i))) : ↥(primesOf (pb 0 * pb 1)) :=
  ⟨v.1, mem_primesOf.2 ⟨mul_ne_zero (pb_ne_zero hT 0) (pb_ne_zero hT 1), by
    have hv := (mem_primesOf.1 v.2).2
    fin_cases i
    · exact Ideal.mul_mem_right _ _ hv
    · exact Ideal.mul_mem_left _ _ hv⟩⟩

def resIso (hT : IsTypeDatum gp pb) (i : Fin 2) (v : ↥(primesOf (pb i))) : ZMod (gp i) ≃+* kP v.1 :=
  have hc : Nat.card (kP v.1) = gp i := hT.deg1 i v.1 (mem_primesOf.1 v.2).2
  have : Finite (kP v.1) := Nat.finite_of_card_ne_zero (by rw [hc]; exact (hT.prime i).ne_zero)
  letI : Fintype (kP v.1) := Fintype.ofFinite _
  ZMod.ringEquivOfPrime (kP v.1) (hT.prime i) (by rw [← Nat.card_eq_fintype_card, hc])

def compAt (hT : IsTypeDatum gp pb) {r : ℕ} (i : Fin 2) (v : ↥(primesOf (pb i)))
    (t : G0 (primesOf (pb 0 * pb 1)) r) : GL (Fin r) (ZMod (gp i)) :=
  Matrix.GeneralLinearGroup.map ((resIso hT i v).symm : kP v.1 →+* ZMod (gp i)) (t (toBoth hT i v))

variable [∀ i, Fact (gp i).Prime] {K : Type} [Field K]

def IsGoodTuple (hT : IsTypeDatum gp pb) (r m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ)
    (ω : ∀ i, Fbar (gp i) →*₀ ℂ) (f : ∀ i, ↥(primesOf (pb i)) → (ZMod (gp i))[X]) : Prop :=
  ∀ i, ∃ c : ↥(primesOf (pb i)) → Fin m → (ZMod (gp i))ˣ,
    (∀ v j, IsTameLabel (ω i)
      (fun z => σ (χ (j.val + 1) v.1 (Units.map ((resIso hT i v : ZMod (gp i) →+* kP v.1) : ZMod (gp i) →* kP v.1) z) : Kˣ))
      (c v j)) ∧
    IsGood r (gp i) (f i) fun v (js : Fin m × Bool) => if js.2 then c v js.1 else (c v js.1)⁻¹

def goodChars (hT : IsTypeDatum gp pb) (r m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ)
    (ω : ∀ i, Fbar (gp i) →*₀ ℂ) : Set (G0 (primesOf (pb 0 * pb 1)) r → ℂ) :=
  {Θ | ∃ (f : ∀ i, ↥(primesOf (pb i)) → (ZMod (gp i))[X])
      (τ : ∀ i, ↥(primesOf (pb i)) → GL (Fin r) (ZMod (gp i)) → ℂ),
    IsGoodTuple hT r m σ χ ω f ∧ (∀ i v, IsTypeChar (ω i) (f i v) (τ i v)) ∧
    ∀ t, Θ t = ∏ i, ∏ v, τ i v (compAt hT i v t)}

end BothPrimes

def GoodCharsRealised : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime] (pb : Fin 2 → 𝓞 E)
    (hT : IsTypeDatum gp pb) (r m : ℕ) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ)
    (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (ω : ∀ i, Fbar (gp i) →*₀ ℂ),
    (∀ i, Function.Injective (ω i)) →
    (∃ ζ : K, IsPrimitiveRoot ζ (Nat.card (G0 (primesOf (pb 0 * pb 1)) r))) →
    (∀ Θ ∈ goodChars hT r m σ χ ω, ∃ ΘK : G0 (primesOf (pb 0 * pb 1)) r → K,
      (∀ t, σ (ΘK t) = Θ t) ∧ IsAbsIrrChar ΘK) ∧
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K (G0 (primesOf (pb 0 * pb 1)) r),
      (Set.range fun (s : T.S) (t : G0 (primesOf (pb 0 * pb 1)) r) => σ (LinearMap.trace K (T.W s) (T.tau s t))) =
        goodChars hT r m σ χ ω

end GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalInducedCharacter
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

def IsCuspIndChar {F : Type} [Field F] {r : ℕ} (θ : GL (Fin r) F → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (σ : Representation ℂ (blockTri (κ := F) b) V),
    IsCuspDatum b σ ∧ ∀ g : GL (Fin r) F, θ g = LinearMap.trace ℂ _ (parInd b σ g)

abbrev kField {E : Type} [Field E] [NumberField E] (PP : Pl E) : Field (kP PP) :=
  Ideal.Quotient.field PP.asIdeal

def IsCuspIndProdChar {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsCuspIndChar (kP PP.1) (kField PP.1) r (θ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) = ∏ PP : ↥Pg, θ PP (g PP)

theorem finite_boundedLevelClassGroupFamily {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  haveI : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : ∀ PP : ↥Pg, Finite (GL (Fin r) (kP PP.1)) := fun PP => inferInstance
  exact Pi.finite

abbrev fintypeH {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [CommRing K]
    (P : LevelP Pg r K) : Fintype P.H :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  Fintype.ofFinite _

def lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  letI := fintypeH P
  ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def OneWhittakerVector : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsCuspIndProdChar Pg r s χ →
      lvlSum (P0 Pg r ψ) χ = (Nat.card (P0 Pg r ψ).H : K)

def OneWhittakerVectorDim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) [Fintype (G0 Pg r)]
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    IsGenericPsi Pg ψ →
    ∀ (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K (G0 Pg r)) (t : T.S),
      IsCuspIndProdChar Pg r s (fun g => LinearMap.trace K (T.W t) (T.tau t g)) →
      Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨(P0 Pg r ψ).H, (P0 Pg r ψ).chi⟩ t = 1

example {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (h : ∀ x : P.H, χ x = (P.chi x : K)) :
    lvlSum P χ = (Nat.card P.H : K) := by
  unfold lvlSum
  letI := fintypeH P
  simp [h, Nat.card_eq_fintype_card]

example {E : Type} [Field E] [NumberField E] (r : ℕ) {K : Type} [Field K] (s : K →+* ℂ) :
    IsCuspIndProdChar (∅ : Finset (Pl E)) r s (fun _ => 1) :=
  ⟨fun _ _ => 1, fun PP => absurd PP.2 (Finset.notMem_empty _), fun g => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameCharacterTorusValues
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

def rootOfOne (q d n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / ((q : ℂ) ^ d - 1))

def torusValue (q d e : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ (d - d / e) * (∏ i ∈ Finset.Ico 1 (d / e), ((q : ℂ) ^ (e * i) - 1)) *
    ∑ i ∈ Finset.range e, z ^ (n * q ^ i)

example (q n : ℕ) (z : ℂ) : torusValue q 1 1 z n = z ^ n := by simp [torusValue]

example (q d : ℕ) (z : ℂ) : torusValue q d 1 z 0 = ∏ i ∈ Finset.Ico 1 d, ((q : ℂ) ^ i - 1) := by
  simp [torusValue]

example (q n : ℕ) (z : ℂ) : torusValue q 2 2 z n = -(z ^ n + z ^ (n * q)) := by
  simp [torusValue, Finset.sum_range_succ]

section Local

variable {g : ℕ} [Fact g.Prime] {r : ℕ}

def blkSize (b : Fin r → ℕ) (c : ℕ) : ℕ := (Finset.univ.filter fun a => b a = c).card

structure IsLabelledDatum (ι : (Fbar g)ˣ →* ℂˣ) (b : Fin r → ℕ) (fac : ℕ → (ZMod g)[X]) {n : ℕ}
    (σ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)) : Prop where
  cusp : IsCuspDatum b σ
  monic : ∀ c ∈ Finset.univ.image b, (fac c).Monic
  irred : ∀ c ∈ Finset.univ.image b, Irreducible (fac c)
  ne_X : ∀ c ∈ Finset.univ.image b, fac c ≠ X
  degree : ∀ c ∈ Finset.univ.image b, (fac c).natDegree = blkSize b c
  value : ∀ (x y : ℕ → (Fbar g)ˣ) (m : ℕ → ℕ) (p : blockTri (κ := ZMod g) b),
    (∀ c ∈ Finset.univ.image b, aeval ((x c : (Fbar g)ˣ) : Fbar g) (fac c) = 0) →
    (∀ c ∈ Finset.univ.image b,
      minpoly (ZMod g) (blkMat b c p) = minpoly (ZMod g) ((y c : (Fbar g)ˣ) : Fbar g)) →
    (∀ c ∈ Finset.univ.image b, ((ι (y c) : ℂˣ) : ℂ) = rootOfOne g (blkSize b c) (m c)) →
    σ.character p = ∏ c ∈ Finset.univ.image b,
      torusValue g (blkSize b c) (minpoly (ZMod g) ((y c : (Fbar g)ˣ) : Fbar g)).natDegree
        ((ι (x c) : ℂˣ) : ℂ) (m c)

def IsTypeChar (ι : (Fbar g)ˣ →* ℂˣ) (s : (ZMod g)[X]) (ch : GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (fac : ℕ → (ZMod g)[X]) (n : ℕ)
    (σ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)),
    IsLabelledDatum ι b fac σ ∧ s = ∏ c ∈ Finset.univ.image b, fac c ∧
      ∀ t, ch t = (parInd b σ).character t

def IsCharLabel (ι : (Fbar g)ˣ →* ℂˣ) (θ : (ZMod g)ˣ → ℂ) (a : (ZMod g)ˣ) : Prop :=
  ∀ (y : (ZMod g)ˣ) (m : ℕ),
    ((ι (Units.map (algebraMap (ZMod g) (Fbar g) : ZMod g →* Fbar g) y) : ℂˣ) : ℂ) = rootOfOne g 1 m →
    θ y = ((ι (Units.map (algebraMap (ZMod g) (Fbar g) : ZMod g →* Fbar g) a) : ℂˣ) : ℂ) ^ m

example (ι : (Fbar g)ˣ →* ℂˣ) : IsCharLabel ι (fun _ => 1) 1 := by
  intro y m _; simp

def lineRep (θ : (ZMod g)ˣ →* ℂˣ) :
    Representation ℂ (blockTri (κ := ZMod g) (fun _ : Fin 1 => 0)) (Fin 1 → ℂ) where
  toFun p := ((θ (blkDet (fun _ : Fin 1 => 0) 0 p) : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by
    rw [map_one, map_one, Units.val_one, one_smul]; rfl
  map_mul' p q := by
    rw [map_mul, map_mul, Units.val_mul, mul_smul]
    ext1 v
    ext i
    simp [mul_left_comm]

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

abbrev typePlaces (pb : Fin 2 → 𝓞 E) : Finset (Pl E) := primesOf (pb 0 * pb 1)

abbrev PlacesOver (pb : Fin 2 → 𝓞 E) (i : Fin 2) : Type :=
  {v : ↥(typePlaces pb) // pb i ∈ v.1.asIdeal}

variable {K : Type} [Field K]

def tameChar (emb : K →+* ℂ) (χ : ℕ → ∀ w : Pl E, (kP w)ˣ →* Kˣ) {m g : ℕ} (w : Pl E) (e : kP w ≃+* ZMod g)
    (j : Fin m × Bool) (y : (ZMod g)ˣ) : ℂ :=
  emb (((if j.2 then χ (j.1.val + 1) w else (χ (j.1.val + 1) w)⁻¹)
    (Units.map (e.symm : ZMod g →* kP w) y) : Kˣ) : K)

open Classical in

def goodChars (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime] (pb : Fin 2 → 𝓞 E) (r m : ℕ)
    (e : ∀ i, ∀ v : PlacesOver pb i, kP v.1.1 ≃+* ZMod (gp i))
    (ι : ∀ i, PlacesOver pb i → ((Fbar (gp i))ˣ →* ℂˣ))
    (emb : K →+* ℂ) (χ : ℕ → ∀ w : Pl E, (kP w)ˣ →* Kˣ) : Set (G0 (typePlaces pb) r → ℂ) :=
  {ch | ∃ (s : ∀ i, PlacesOver pb i → (ZMod (gp i))[X])
      (lab : ∀ i, PlacesOver pb i → Fin m × Bool → (ZMod (gp i))ˣ)
      (loc : ∀ i, PlacesOver pb i → GL (Fin r) (ZMod (gp i)) → ℂ),
      (∀ i v j, IsCharLabel (ι i v) (tameChar emb χ v.1.1 (e i v) j) (lab i v j)) ∧
      (∀ i, IsGood r (gp i) (s i) (lab i)) ∧
      (∀ i v, IsTypeChar (ι i v) (s i v) (loc i v)) ∧
      ∀ t, ch t = ∏ i, ∏ v : PlacesOver pb i,
        loc i v (Matrix.GeneralLinearGroup.map (e i v : kP v.1.1 →+* ZMod (gp i)) (t v.1))}

end Global

def GoodCharsGoodFamily : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime]
    (pb : Fin 2 → 𝓞 E), IsTypeDatum gp pb → ∀ (r m : ℕ)
    (e : ∀ i, ∀ v : PlacesOver pb i, kP v.1.1 ≃+* ZMod (gp i))
    (ι : ∀ i, PlacesOver pb i → ((Fbar (gp i))ˣ →* ℂˣ)), (∀ i v, Function.Injective (ι i v)) →
    ∀ (K : Type) [Field K] [NumberField K] (emb : K →+* ℂ),
    (∃ ζ : K, IsPrimitiveRoot ζ (Nat.card (G0 (typePlaces pb) r))) →
    ∀ χ : ℕ → ∀ w : Pl E, (kP w)ˣ →* Kˣ,
    ∃ Xg : Finset (G0 (typePlaces pb) r → K),
      (∀ ch, ch ∈ goodChars gp pb r m e ι emb χ ↔ ∃ c ∈ Xg, ∀ t, ch t = emb (c t)) ∧
      (∀ c ∈ Xg, IsAbsIrrChar c) ∧
      ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K (G0 (typePlaces pb) r),
        ∀ c, c ∈ Xg ↔ ∃ s : T.S, ∀ t, c t = LinearMap.trace K (T.W s) (T.tau s t)

end GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues
end
end

