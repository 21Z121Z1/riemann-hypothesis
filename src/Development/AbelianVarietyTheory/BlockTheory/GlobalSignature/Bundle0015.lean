import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ScalarCharacterTwist
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScalarCharacterTwist

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)

def HasVal_vp (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) (r : ℚ) : Prop :=
  ∃ (n : ℕ) (k : K), 0 < n ∧ k ≠ 0 ∧ σ k = z ^ n ∧ (ordE w k : ℚ) = (n : ℚ) * r * (eW w : ℚ)

def UnitAtW (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) : Prop := HasVal_vp σ w z 0

def ModOne (z : ℂ) : Prop :=
  ∃ (n : ℕ) (k : K), 0 < n ∧ σ k = z ^ n ∧ ∀ φ : K →+* ℂ, ‖φ k‖ = 1

theorem ordE_pow (w : HeightOneSpectrum (𝓞 K)) (k : K) (n : ℕ) : ordE w (k ^ n) = n * ordE w k := by
  unfold ordE
  rw [map_pow, WithZero.log_pow]
  simp

theorem hasVal_vp_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) (r : ℚ) :
    HasVal_vp σ w (σ k) r ↔ k ≠ 0 ∧ (ordE w k : ℚ) = r * (eW w : ℚ) := by
  constructor
  · rintro ⟨n, k', hn, hk', h1, h2⟩
    have h3 : k' = k ^ n := σ.injective (by rw [h1, map_pow])
    subst h3
    refine ⟨fun h => hk' (by rw [h, zero_pow hn.ne']), ?_⟩
    rw [ordE_pow] at h2
    push_cast at h2
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hn'
    rw [h2, mul_assoc]
  · rintro ⟨h0, h⟩
    exact ⟨1, k, one_pos, h0, by rw [pow_one], by rw [h]; simp⟩

theorem unitAtW_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) : UnitAtW σ w (σ k) ↔ w.valuation K k = 1 := by
  unfold UnitAtW
  rw [hasVal_vp_iff, zero_mul]
  constructor
  · rintro ⟨h0, h⟩
    have h1 : w.valuation K k ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : WithZero.log (w.valuation K k) = 0 := by
      have : ordE w k = 0 := by exact_mod_cast h
      unfold ordE at this
      omega
    rw [← WithZero.exp_log h1, h2, WithZero.exp_zero]
  · intro h
    refine ⟨fun h0 => by simp [h0] at h, ?_⟩
    unfold ordE
    rw [h]
    simp

theorem modOne_iff (k : K) : ModOne σ (σ k) ↔ ∀ φ : K →+* ℂ, ‖φ k‖ = 1 := by
  constructor
  · rintro ⟨n, k', hn, h1, h2⟩ φ
    have h3 : k' = k ^ n := σ.injective (by rw [h1, map_pow])
    have h4 := h2 φ
    rw [h3, map_pow, norm_pow] at h4
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4
  · intro h
    exact ⟨1, k, one_pos, by rw [pow_one], h⟩

end Val

section Cls

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def vpLat (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E 1) where
  carrier := {x | ∀ y ∈ (conjPrime₂ P).asIdeal, ∃ z ∈ P.asIdeal, algebraMap (𝓞 E) E z = algebraMap (𝓞 E) E y * x 0}
  zero_mem' := fun _ _ => ⟨0, P.asIdeal.zero_mem, by simp⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z, hz, e⟩ := ha y hy
    obtain ⟨z', hz', e'⟩ := hb y hy
    refine ⟨z + z', P.asIdeal.add_mem hz hz', ?_⟩
    rw [map_add, e, e', Pi.add_apply, mul_add]
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, hz, e⟩ := ha y hy
    refine ⟨c * z, P.asIdeal.mul_mem_left c hz, ?_⟩
    rw [map_mul, e, Pi.smul_apply, Algebra.smul_def]
    ring

def FrOf {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) : Prop :=
  ∀ (P : SB) (x : Sp E n), fr P x ∈ localization₂ P.1.asIdeal N ↔ x ∈ stdAt E n P.1

def DetUnitAt {n : ℕ} (ST : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P ∈ ST, ordDet P N = 0

def StdAt {n : ℕ} (ST : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P ∈ ST, localization₂ P.asIdeal N = stdAt E n P

end Cls

section Chars

variable {D : Dat} {H : D7} (s : Seam H D.X) (χ : TaylorLogMetric.IdE H → ℂ)
  (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) {S : Set ℕ}
  (mu : Tup D.X.F D.X.E D.X.K S) (cst : LocCst D.X (rowSG D.Pr sel mu))

def chiDet {n : ℕ} (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) : ℂ := χ (TaylorLogMetric.detId H (StandardLatticesGL3.stdL H n) (s.lat N))

def muOffJ (i : ℕ) {n : ℕ} (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) : D.X.K :=
  muOff sel (rowSG D.Pr sel mu) (mUof D.Ch mu i) N

def muInvJ (i : ℕ) {n : ℕ} (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) (fr : Frs D.X.E n (rowSG D.Pr sel mu)) : D.X.K :=
  muInvDet sel (rowSG D.Pr sel mu) (mUof D.Ch mu i) (muAtT D.Ch sel mu cst i) N fr

def rhoJ (i : ℕ) {n : ℕ} (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) (fr : Frs D.X.E n (rowSG D.Pr sel mu)) : ℂ :=
  s.σ₀ (muInvJ sel mu cst i N fr) * chiDet s χ N ^ (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))

def rhoJ' (i : ℕ) {n : ℕ} (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) (fr : Frs D.X.E n (rowSG D.Pr sel mu)) : ℂ :=
  (s.σ₀ (muInvJ sel mu cst i N fr))⁻¹ * chiDet s χ N ^ ((D.R.N i / 2 : ℕ) : ℤ)

def scalJ (i : ℕ) (N : Submodule (𝓞 D.X.E) (Sp D.X.E (D.R.N i))) (fr : Frs D.X.E (D.R.N i) (rowSG D.Pr sel mu))
    (N' : Submodule (𝓞 D.X.E) (Sp D.X.E (D.R.N (i + 1)))) (fr' : Frs D.X.E (D.R.N (i + 1)) (rowSG D.Pr sel mu)) : D.X.K :=
  muInvJ sel mu cst i N fr * (muInvJ sel mu cst i N' fr')⁻¹

def chiFJ (a b : ℕ) (N : Submodule (𝓞 D.X.E) (Sp D.X.E a)) (N' : Submodule (𝓞 D.X.E) (Sp D.X.E b)) : ℂ :=
  Base.chiFac χ a b (s.lat N) (s.lat N')

def sPrime (D : Dat) (i : Fin D.R.m) (τ : D.X.Tau) : ℚ := (D.W.row τ).e i - (D.R.N (i.1 + 1) : ℚ) / 2

def sExp (D : Dat) (i : Fin D.R.m) (τ : D.X.Tau) : ℚ := (D.W.row τ).e i - (D.R.N i.1 : ℚ) / 2

def OverT (D : Dat) (u : D.Pr.Word) (w : HeightOneSpectrum (𝓞 D.X.K)) : Prop := ((D.Pr.T u : ℕ) : 𝓞 D.X.K) ∈ w.asIdeal

def PartA (u : D.Pr.Word) : Prop :=
  ∀ P ∈ D.Pr.vT u,
    ModOne s.σ₀ (chiDet s χ (vpLat P)) ∧
    (∀ w, ¬ OverT D u w → UnitAtW s.σ₀ w (chiDet s χ (vpLat P))) ∧
    (∀ w, seenC D.Pr u w → HasVal_vp s.σ₀ w (chiDet s χ (vpLat P)) (-1)) ∧
    (∀ w, seenBarC D.Pr u w → HasVal_vp s.σ₀ w (chiDet s χ (vpLat P)) 1)

def PartB (u : D.Pr.Word) : Prop :=
  ∀ w, OverT D u w → ∀ (i : Fin D.R.m) (n : ℕ) (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) (fr : Frs D.X.E n (rowSG D.Pr sel mu)),
    IsSdLat N → FrOf N fr → DetUnitAt (D.Pr.vT u) N →
      UnitAtW s.σ₀ w (chiDet s χ N) ∧ UnitAtW s.σ₀ w (rhoJ s χ sel mu cst i N fr) ∧ UnitAtW s.σ₀ w (rhoJ' s χ sel mu cst i N fr) ∧
      w.valuation D.X.K (muOffJ sel mu i N) = 1 ∧ w.valuation D.X.K (muInvJ sel mu cst i N fr) = 1

def PartBStd (u : D.Pr.Word) : Prop :=
  ∀ w, OverT D u w → ∀ (i : Fin D.R.m)
    (N : Submodule (𝓞 D.X.E) (Sp D.X.E (D.R.N i))) (fr : Frs D.X.E (D.R.N i) (rowSG D.Pr sel mu))
    (N' : Submodule (𝓞 D.X.E) (Sp D.X.E (D.R.N (i + 1)))) (fr' : Frs D.X.E (D.R.N (i + 1)) (rowSG D.Pr sel mu)),
    IsSdLat N → IsSdLat N' → FrOf N fr → FrOf N' fr' → StdAt (D.Pr.vT u) N → StdAt (D.Pr.vT u) N' →
      UnitAtW s.σ₀ w (chiFJ s χ (D.R.N i) (D.R.N (i + 1)) N N') ∧
      w.valuation D.X.K (muOffJ sel mu i N) = 1 ∧ w.valuation D.X.K (muOffJ sel mu i N') = 1 ∧
      w.valuation D.X.K (muInvJ sel mu cst i N fr) = 1 ∧ w.valuation D.X.K (muInvJ sel mu cst i N' fr') = 1 ∧
      w.valuation D.X.K (scalJ sel mu cst i N fr N' fr') = 1

def PartC (u : D.Pr.Word) : Prop :=
  ∀ w, OverT D u w → ∀ (i : Fin D.R.m), ∀ P ∈ D.Pr.vT u, ∀ τ : D.X.Tau, (SeesP w τ P ∨ SeesPbar w τ P) →
    ∀ r : ℚ, HasVal_vp s.σ₀ w (chiDet s χ (vpLat P)) r →
      HasVal_vp s.σ₀ w (rhoJ s χ sel mu cst i (vpLat P) fun _ => 1) (sPrime D i τ * r) ∧
      HasVal_vp s.σ₀ w (rhoJ' s χ sel mu cst i (vpLat P) fun _ => 1) (-(sExp D i τ) * r)

def PartD : Prop :=
  ∀ (i : Fin D.R.m) (n : ℕ) (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) (fr : Frs D.X.E n (rowSG D.Pr sel mu)),
    IsSdLat N → FrOf N fr →
      rhoJ s χ sel mu cst i N fr * rhoJ' s χ sel mu cst i N fr = chiDet s χ N ^ (-(((D.R.t + 1) / 2 : ℕ) : ℤ))

def UnrTG (u : D.Pr.Word) : Prop :=
  ∀ v ∈ Qprime (mu : Chr D.X.F D.X.E D.X.K), ((D.Pr.T u : ℕ) : 𝓞 D.X.F) ∉ v.asIdeal ∧ ∀ i, ((D.Pr.g i : ℕ) : 𝓞 D.X.F) ∉ v.asIdeal

end Chars

def CharValuations : Prop :=
  ∀ (D : Dat), D.Ok → ∀ (H : D7) (s : Seam H D.X), s.Ok → s.σ₀ = D.sig0 → ∀ χ : TaylorLogMetric.IdE H → ℂ, TaylorLogMetric.IsChi H χ →
  ∀ u : D.Pr.Word,
    PartA s χ u ∧
    ∀ (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)), IsSel D.X sel →
    ∀ (S : Set ℕ) (mu : Tup D.X.F D.X.E D.X.K S), UnrTG mu u →
    ∀ (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.X.E) (eta : Formalism.L2.Host.HChar D.X.E),
      D.Ch.Tied D.sig0 (fun j τ => (D.W.row τ).e j) m0 eta →
    ∀ cst : LocCst D.X (rowSG D.Pr sel mu), MuqTieG sel mu cst D.sig0 m0 →
      PartB s χ sel mu cst u ∧ PartBStd s χ sel mu cst u ∧ PartC s χ sel mu cst u ∧ PartD s χ sel mu cst

end GlobalTheory.IndefiniteRowSideFullHecke.ScalarCharacterTwist
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardKernelAtTorus
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardKernelAtTorus

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Adjoint

variable {E : Type} [Field E] [StarRing E] {a b : ℕ}

def adj (x : HomE E a b) : HomE E b a where
  toFun w := fun α => ∑ β : Fin b, star (x (Pi.single α 1) β) * w β
  map_add' w w' := by funext α; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c w := by funext α; simp [Finset.mul_sum, mul_left_comm]

theorem adj_single (x : HomE E a b) (β : Fin b) (α : Fin a) :
    adj x (Pi.single β 1) α = star (x (Pi.single α 1) β) := by
  simp [adj, Pi.single_apply]

end Adjoint

section Sets

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def StdAtT {n : ℕ} (d : Deco E n ST SG) : Prop := ∀ P : ST, d.at P.1 = stdAt E n P.1

def suppPts (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}

def dualPts (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d'.at P.1, d'.f P y = 0 → adj x y ∈ d.at P.1}

end Sets

section Table

variable {X : Fields} {a b : ℕ}

def diracMom {p : ℕ} [Fact p.Prime] (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) (x : HomE X.E a b)
    (m : DVar X.Tau a b →₀ ℕ) : ℂ_[p] :=
  m.prod fun k n => (uu k.1 * ι (X.emb k.1 (adj x (Pi.single k.2.1 1) k.2.2))) ^ n

def kerTable (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)
    (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => Ξ x * A.jetK Sall N N' cB x m

def RatAt (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)
    (m : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ x ∈ divLat cA (homAt Sall N N'), Ξ x ≠ 0 →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m

def InMomClosure {p : ℕ} [Fact p.Prime] {I H : Type} (G : Set I) (t : I → ℂ_[p]) (κ : ℂ_[p]) (Z : Set H) (mom : H → I → ℂ_[p]) : Prop :=
  ∀ M : Finset I, (∀ m ∈ M, m ∈ G) → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (z : Fin n → H), (∀ i, ‖r i‖ ≤ 1) ∧ (∀ i, z i ∈ Z) ∧
      ∀ m ∈ M, ‖t m - κ * ∑ i, r i * mom (z i) m‖ < ε

end Table

def Induces {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ k : 𝓞 K, ‖ι (k : K)‖ < 1 ↔ k ∈ w.asIdeal

def OffT {E : Type} [Field E] [NumberField E] [StarRing E] (SB : Finset (HeightOneSpectrum (𝓞 E))) (q₁ c T : ℕ) : Prop :=
  ∀ P ∈ SB, conjPrime₂ P ∉ SB ∧ ((2 : ℕ) : 𝓞 E) ∉ P.asIdeal ∧ (q₁ : 𝓞 E) ∉ P.asIdeal ∧ (c : 𝓞 E) ∉ P.asIdeal ∧ (T : 𝓞 E) ∉ P.asIdeal

def DatumOffT {X : Fields} {a b : ℕ} (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB' : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (w : HeightOneSpectrum (𝓞 X.K))
    (Φ : HomE X.E a b → X.K) : Prop :=
  (∀ x ∈ divLat cA (homAt Sall N N'), ∀ x' ∈ divLat cA (homAt Sall N N'), x - x' ∈ mulLat cB' (homAt SB N N') → Φ x = Φ x') ∧
  ∀ x ∈ divLat cA (homAt Sall N N'), w.valuation X.K (Φ x) ≤ 1

def MomAt {X : Fields} (A : Amb X) (Pr : Primes X) (u : Pr.Word) (good : Finset (HeightOneSpectrum (𝓞 X.E)) → Prop)
    {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 X.K)) (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) : Prop :=
  ∀ (a b : ℕ), Even a → Even b →
  ∀ (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))), good SB → (∀ P, P ∈ Sall ↔ P ∈ Pr.vT u ∨ P ∈ SB) →
  ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))) (d : DecoSet X.E a (Pr.vT u) SG) (d' : DecoSet X.E b (Pr.vT u) SG'),
    StdAtT d.1 → StdAtT d'.1 →
  ∀ (cA cB' : ℕ), Nat.Coprime cA (Pr.T u) → Nat.Coprime cB' (Pr.T u) →
  ∀ Φ : HomE X.E a b → X.K, DatumOffT SB Sall cA cB' d.1.N d'.1.N w Φ →
    (seenBarC Pr u w →
      InMomClosure {m | RatAt A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m}
        (fun m => ι (kerTable A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m))
        1 (suppPts d.1 d'.1) (diracMom ι uu)) ∧
    (seenC Pr u w →
      InMomClosure {m | RatAt A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m}
        (fun m => ι (kerTable A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m))
        (((p : ℂ_[p]) ^ (X.f * a))⁻¹) (dualPts d.1 d'.1) (diracMom ι uu))

def MomT : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok →
  ∀ (Pr : Primes X), Pr.Ok → X.IsCond Pr.cond →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), TaylorLogMetric.IsChi D χ → IsDgen D cD →
  ∀ (u : Pr.Word), Nat.Coprime (Ideal.absNorm cc) (Pr.T u) →
  ∀ (p : ℕ) [Fact p.Prime], p = Pr.T u →
  ∀ (w : HeightOneSpectrum (𝓞 X.K)) (ι : X.K →+* ℂ_[p]), Induces ι w →
    ∃ uu : X.Tau → ℂ_[p], (∀ τ, ‖uu τ‖ = 1) ∧
      MomAt (ambOf s B χ cD) Pr u (fun SB => OffT SB D.host.q (Ideal.absNorm cc) (Pr.T u)) w ι uu

end GlobalTheory.IndefiniteRowSideFullHecke.StandardKernelAtTorus
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
section
open NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

def ptTable {R : Type} [CommRing R] {ι : Type} {a b : ℕ} (ap : ι → Matrix (Fin a) (Fin b) R)
    (m : DVar ι a b →₀ ℕ) : R :=
  m.prod fun k e => ap k.1 k.2.2 k.2.1 ^ e

def substAdj {K : Type} [Field K] {ι : Type} {a b : ℕ} (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) K) :
    Pol K ι a →ₐ[K] Pol K ι b :=
  aeval fun v => ∑ β : Fin b, C (ap v.1 v.2.1 β) * X (v.1, β, Fin.castLE hab v.2.2)

def sharp {K : Type} [Field K] {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (P : Pol K ι a) : Pol K ι a :=
  P * ∏ τ, frDet K a τ ^ n τ

def evalFr {K : Type} [Field K] {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) K) (P : Pol K ι a) : K :=
  eval (fun v : ι × Fin a × Fin a => y v.1 v.2.1 v.2.2) P

def fnOf {K : Type} [Field K] {ι : Type} [Fintype ι] {a : ℕ} (lam : ι → DomWeight a) (P : Pol K ι a)
    (y : ι → GL (Fin a) K) : K :=
  evalFr (fun τ => (y τ : Matrix (Fin a) (Fin a) K)) P *
    ∏ τ, (y τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift

def WtCompat {ι : Type} {a b : ℕ} (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (s s' : ι → ℤ) (n : ι → ℕ) : Prop :=
  (∀ τ (i : Fin a), (lam' τ).w (Fin.castLE hab.le i) + s τ = (lam τ).w i + s' τ) ∧
  (∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).w j = -s τ) ∧
  ∀ τ, (n τ : ℤ) = (lam τ).detShift + s' τ

def InDeg {ι : Type} {a b : ℕ} (lam : ι → DomWeight a) (s' : ι → ℤ) (m : DVar ι a b →₀ ℕ) : Prop :=
  ∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) = ∑ i : Fin a, ((lam τ).w i + s' τ)

section Lat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

def HAt {a : ℕ} (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) :
    Submodule (𝓞 K) (VV K lam) :=
  localization₂ w.asIdeal (nabK lam fun τ => dualFr (M τ))

def detFac {a b : ℕ} (s s' : ι → ℤ) (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K) : K :=
  ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ * (BW τ : Matrix (Fin b) (Fin b) K).det ^ (-s τ)

def LatWithBasis {a : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin a → K))
    (B : ι → GL (Fin a) K) : Prop :=
  ∀ τ, (M τ).FG ∧ IsBasisAt w (M τ) (B τ)

def extLat {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a : ℕ}
    (M : Submodule (𝓞 K) (Fin a → K)) : Submodule v.integer (Fin a → L) :=
  Submodule.span v.integer ((fun (x : Fin a → K) (i : Fin a) => σ (x i)) '' (M : Set (Fin a → K)))

def admitted {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a b : ℕ}
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (ap : ι → Matrix (Fin a) (Fin b) L) : Prop :=
  ∀ τ, ∀ y ∈ extLat v σ (MW τ), ap τ *ᵥ y ∈ extLat v σ (M τ)

def InClosure {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a b : ℕ}
    (lam : ι → DomWeight a) (s' : ι → ℤ)
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (κ : K) (J : (DVar ι a b →₀ ℕ) → K) : Prop :=
  ∀ ε : K, ε ≠ 0 → ∃ (k : ℕ) (c : Fin k → L) (ap : Fin k → ι → Matrix (Fin a) (Fin b) L),
    (∀ i, v (c i) ≤ 1) ∧ (∀ i, admitted v σ M MW (ap i)) ∧
    ∀ m, InDeg lam s' m → v (σ (J m) - σ κ * ∑ i, c i * ptTable (ap i) m) ≤ v (σ ε)

end Lat

def Substitution : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (ap : ι → Matrix (Fin a) (Fin b) K) (F : VV K lam),
      ((jetOp lam lam' (ptTable ap) n F : VV K lam') : Pol K ι b) = substAdj hab.le ap (sharp n (F : Pol K ι a)) ∧
      (∀ y : ι → GL (Fin a) K, evalFr (fun τ => (y τ : Matrix (Fin a) (Fin a) K)) (sharp n (F : Pol K ι a)) =
        fnOf lam (F : Pol K ι a) y * ∏ τ, (y τ : Matrix (Fin a) (Fin a) K).det ^ s' τ) ∧
      ∀ y' : ι → GL (Fin b) K,
        fnOf lam' ((jetOp lam lam' (ptTable ap) n F : VV K lam') : Pol K ι b) y' =
          evalFr (fun τ => (ap τ * (y' τ : Matrix (Fin b) (Fin b) K)).submatrix id (Fin.castLE hab.le))
              (sharp n (F : Pol K ι a)) /
            ∏ τ, (y' τ : Matrix (Fin b) (Fin b) K).det ^ s τ

def DetIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r : ℕ) (B B' : GL (Fin r) K)
    (M' : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (q : K), q ≠ 0 →
    localization₂ w.asIdeal M' = localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun α : Fin r =>
      (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j)) →
    IsBasisAt w M' B' →
    w.valuation K (B' : Matrix (Fin r) (Fin r) K).det = w.valuation K (q * (B : Matrix (Fin r) (Fin r) K).det)

def PointIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
      (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K), LatWithBasis w M B → LatWithBasis w MW BW →
    ∀ ap : ι → Matrix (Fin a) (Fin b) K, (∀ τ, ∀ y ∈ MW τ, ap τ *ᵥ y ∈ localization₂ w.asIdeal (M τ)) →
    ∀ F ∈ HAt w lam M, ∃ G ∈ HAt w lam' MW, jetOp lam lam' (ptTable ap) n F = detFac s s' B BW • G

def ClosureIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L),
    (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
      (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
      (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K), LatWithBasis w M B → LatWithBasis w MW BW →
    ∀ (κ : K) (J : (DVar ι a b →₀ ℕ) → K), InClosure v σ lam s' M MW κ J →
    ∀ F ∈ HAt w lam M, ∃ G ∈ HAt w lam' MW, jetOp lam lam' J n F = (κ * detFac s s' B BW) • G

def JetPointStatement : Prop := Substitution ∧ DetIndex ∧ PointIntegral ∧ ClosureIntegral

example : WtCompat (ι := Unit) (a := 1) (b := 2) (by norm_num)
    (fun _ => ⟨fun _ => 3, fun _ _ _ => le_rfl⟩)
    (fun _ => ⟨![4, -1], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩)
    (fun _ => 1) (fun _ => 2) (fun _ => 5) := by
  refine ⟨fun _ i => ?_, fun _ j hj => ?_, fun _ => ?_⟩
  · fin_cases i; rfl
  · fin_cases j
    · simp at hj
    · rfl
  · simp [DomWeight.detShift]

example {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {a b : ℕ} (lam : ι → DomWeight a) (s' : ι → ℤ)
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (ap : ι → Matrix (Fin a) (Fin b) K) (h : admitted v (RingHom.id K) M MW ap) :
    InClosure v (RingHom.id K) lam s' M MW 1 (ptTable ap) :=
  fun _ _ => ⟨1, fun _ => 1, fun _ => ap, fun _ => by simp, fun _ => h, fun m _ => by simp⟩

example {R : Type} [CommRing R] {ι : Type} {a b : ℕ} (ap : ι → Matrix (Fin a) (Fin b) R) (τ : ι) (β : Fin b)
    (α : Fin a) : ptTable ap (Finsupp.single (τ, β, α) 1) = ap τ α β := by
  simp [ptTable]

end GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
end
end

