import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CompLocOfApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def OHat (p : ℕ) (E : Type) [Field E] [NumberField E] : AddSubgroup (AfP p ⊗[ℚ] E) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ (x : E)}

structure AdQ (p : ℕ) where
  ρ : AfQ →+* AfP p
  surj : Function.Surjective ρ
  ker : ∀ a, ρ a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0
  int : ∀ a, IsIntAf (ρ a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1

structure AdT (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] extends AdQ p where
  Φ : Af E →+* AfP p ⊗[ℚ] E
  Φ_E : ∀ x : E, Φ (algebraMap E (Af E) x) = 1 ⊗ₜ x
  Φ_Q : ∀ a : AfQ, Φ (finiteAdeleMap ℚ E a) = ρ a ⊗ₜ 1
  Φ_surj : Function.Surjective Φ
  Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0
  Φ_int : ∀ x, Φ x ∈ OHat p E ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → Valued.v (pLoc E w x) ≤ 1
  Φ_conj : ∀ x, Φ (conjFin (conjE E) x) = conjT E (AfP p) (Φ x)

def AdQEx : Prop := ∀ (p : ℕ) [Fact p.Prime], Nonempty (AdQ p)

def AdTensor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ ι : AfQ ⊗[ℚ] E ≃+* Af E,
  (∀ (a : AfQ) (x : E), ι (a ⊗ₜ x) = finiteAdeleMap ℚ E a * algebraMap E (Af E) x) ∧
  (∀ y, y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} ↔
    ∀ w : Plc E, Valued.v (pLoc E w (ι y)) ≤ 1) ∧
  ∀ a : AfQ, conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a

def IdemP : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E], ∃ e : AfQ,
  (∀ v : Plc ℚ, ((p : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((p : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) ∧
  ∀ w : Plc E, ((p : 𝓞 E) ∈ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 1) ∧
    ((p : 𝓞 E) ∉ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 0)

def AdTEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E], Nonempty (AdT p E)

def IsMu {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : Prop :=
  ∀ (r : R) (x : Matrix (Fin n) (Fin n) E) i k, μ (r ⊗ₜ x) i k = r ⊗ₜ x i k

def MuEx : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ),
  ∃ μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E), IsMu μ

def MuStar : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)), IsMu μ → ∀ x,
  Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ (starT (hermStar (A.H n) (A.det_ne n)) R x).unop =
    ((μ x).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIso (A : Arith E) (n : ℕ) (a : GL (Fin n) (Af E)) : Prop :=
  (a.val.map (conjFin (conjE E)))ᵀ * Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) * a.val = 1 ∧
    ∀ (w : Plc E) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal → GeneralLinearGroup.map (pLoc E w) a ∈ KGL w n

def Arith.β₀ (A : Arith E) (n : ℕ) : (Matrix (Fin n) (Fin n) E)ˣ :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (A.dg n i : E)) (by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this])

variable {A : Arith E} {n p : ℕ} [Fact p.Prime]

def Setup.mx (S : Setup A n p) (h : S.G.GAf) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ((h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] S.G.C)

structure Tr (S : Setup A n p) extends AdT p E where
  μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)
  mu : IsMu μ
  a : GL (Fin n) (Af E)
  iso : IsIso A n a
  j : GUf E n →* S.G.GAf
  j_mx : ∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map Φ
  j_sim : ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = ρ (sim g : AfQˣ)
  sec : S.G.GAf →* GUf E n
  j_sec : ∀ h, j (sec h) = h
  sec_p : ∀ h (w : Plc E), (p : 𝓞 E) ∈ w.asIdeal → comp w (sec h) = 1
  j_eq : ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∃ j : GUf E n →* S.G.GAf,
    (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) ∧
    ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = T.ρ (sim g : AfQˣ)

def JEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ (a : GL (Fin n) (Af E)) (j : GUf E n →* S.G.GAf), (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) →
  (∀ g g' : GUf E n, (∀ w, comp w g = comp w g') → g = g') ∧
  ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JSurj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∀ h : S.G.GAf, ∃ g : GUf E n,
    μ (S.mx h) = (a * mat g * a⁻¹).val.map T.Φ ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g = 1

def IsoEx' : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Odd n → ∃ a, IsIso A n a

def TrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  Odd n → Nonempty (Tr S)

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w)
  (x : GL (Fin n) (w.adicCompletion E)) (g : GUf E n), comp w g = 1 → CertificateRingHomMap.loc hw x * g = g * CertificateRingHomMap.loc hw x

theorem apart_of_not_mem {w u : Plc E} (hw : (p : 𝓞 E) ∉ w.asIdeal) (hu : (p : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart u w := by
  intro h
  apply hw
  have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hu
  rw [h] at h1
  have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  simpa using h2

def Tr.at {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    Loc S.G.GAf (GL (Fin n) (w.adicCompletion E)) where
  pr := (comp w).comp T.sec
  loc := T.j.comp (CertificateRingHomMap.loc hw)
  pr_loc x := by
    have := (T.j_eq (T.sec (T.j (CertificateRingHomMap.loc hw x))) (CertificateRingHomMap.loc hw x)).1 (T.j_sec _) w hp
    simpa using this
  comm x g h := by
    have := congrArg T.j (hc E n w hw x (T.sec g) h)
    simpa [T.j_sec] using this

def LatCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∃ ν : AfP p ⊗[ℚ] VQ S.D ≃+ (Fin n → AfP p ⊗[ℚ] E),
    (∀ (r : AfP p) (v : Fin n → 𝓞 E) i, ν (r ⊗ₜ ((1 : ℚ) ⊗ₜ[ℤ] v)) i = r ⊗ₜ (v i : E)) ∧
    (∀ h v, ν (S.L.actG h v) = μ (S.mx h) *ᵥ ν v) ∧ ∀ v, v ∈ LaHat S.D ↔ ∀ i, ν v i ∈ OHat p E

def Cong1 (N : ℕ) (w : Plc E) (x : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∀ i k, Valued.v ((x.val - 1) i k) ≤ Valued.v (N : w.adicCompletion E)

def KNIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n),
  ((∀ v ∈ LaHat S.D, S.L.actG (T.j g) v ∈ LaHat S.D) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
    Valued.v ((GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val i k) ≤ 1) ∧
  ∀ N : ℕ, 0 < N → (S.L.CongOne N (T.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)))

def StdForm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1) (e : GlobalTheory.LKCx.grp S.G B.β →* Gam0 E n),
    (∀ y, ((e y : Gam0 E n) : GL (Fin n) E × ℚˣ) = (y : S.G.Cˣ × ℚˣ)) ∧ ∀ y, GlobalTheory.LKCx.toAfF S.G B.β x 1 hx y = T.j (rat (e y))

def PInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G →
  (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w n) ∧
    ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal → Valued.v (((sim (rat y) : AfQˣ) : AfQ) v) = 1

def ClsConj : Prop := ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
  (hx : Triv G (AfP p) B.β x t), ∃ (y₀ : G.Cˣ × ℚˣ) (h₀ : G.GAf × Gr G 1)
    (e : GlobalTheory.LKCx.grp G (Quot.out (Quot.mk _ B : DFCls G)).β →* GlobalTheory.LKCx.grp G B.β),
    (∀ γ, ((e γ : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ) = y₀⁻¹ * γ * y₀) ∧
    ∀ γ, (Quot.out (Quot.mk _ B : DFCls G)).emb γ = h₀ * B.embAt x t hx (e γ) * h₀⁻¹

end UpperTheory.Gal.W2.Seed
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma exists_close {E : Type} [Field E] [NumberField E] (c : InfinitePlace E → E) :
    ∃ x : E, ∀ v : InfinitePlace E, v (x - c v) < 1 / 2 := by
  have hd := InfinitePlace.denseRange_algebraMap_pi E
  obtain ⟨x, hx⟩ := hd.exists_dist_lt (fun v : InfinitePlace E => WithAbs.toAbs v.1 (c v))
    (by norm_num : (0:ℝ) < 1/2)
  refine ⟨x, fun v => ?_⟩
  have h1 := (dist_le_pi_dist _ _ v).trans_lt hx
  rw [dist_comm, dist_eq_norm] at h1
  exact h1

theorem UpperTheory.Gal.W2.Seed.pCEx :
    CEx := by
  intro E _ _ _ τ₀ M hM
  classical
  obtain ⟨x, hx⟩ := exists_close (E := E) (fun v => if v = InfinitePlace.mk τ₀ then -1 else 1)
  have hbound : ∀ τ : E →+* ℂ,
      |(τ x).re - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1)| < 1 / 2 := by
    intro τ
    have h : ‖τ (x - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1))‖ < 1 / 2 :=
      hx (InfinitePlace.mk τ)
    refine lt_of_le_of_lt ?_ h
    split_ifs with hτ
    · have := Complex.abs_re_le_norm (τ x - -1)
      simpa using this
    · have := Complex.abs_re_le_norm (τ x - 1)
      simpa using this
  have hxalg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple hxalg
  set z : E := y • (y • x) with hzdef
  have hz : IsIntegral ℤ z := hyint.smul y
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hy2 : 0 < (y : ℝ) ^ 2 := by positivity
  have hτz : ∀ τ : E →+* ℂ, (τ z).re = (y : ℝ) ^ 2 * (τ x).re := by
    intro τ
    simp [hzdef, zsmul_eq_mul]
    ring
  set w : E := z + IsCMField.complexConj E z with hwdef
  have hw : IsIntegral ℤ w := hz.add (map_isIntegral_int (IsCMField.complexConj E) hz)
  have hτw : ∀ τ : E →+* ℂ, (τ w).re = 2 * (τ z).re := by
    intro τ
    simp [hwdef, IsCMField.complexEmbedding_complexConj]
    ring
  have hneg : (τ₀ w).re < 0 := by
    have hb := hbound τ₀
    rw [if_pos rfl] at hb
    have := (abs_lt.mp hb).2
    rw [hτw, hτz]
    nlinarith
  have hpos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ w).re := by
    intro τ hτ
    have hb := hbound τ
    rw [if_neg hτ] at hb
    have := (abs_lt.mp hb).1
    rw [hτw, hτz]
    nlinarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ((M : ℝ) * -(τ₀ w).re))
  have hKM : 1 < (M : ℝ) * K * -(τ₀ w).re := by
    have hd : 0 < (M : ℝ) * -(τ₀ w).re := by nlinarith
    rw [div_lt_iff₀ hd] at hK
    nlinarith
  let wO : 𝓞 E := ⟨w, (mem_integralClosure_iff ℤ E).mpr hw⟩
  have hcoe : (((1 : 𝓞 E) + (M : 𝓞 E) * ((K : 𝓞 E) * wO) : 𝓞 E) : E) = 1 + (M : E) * ((K : E) * w) := by
    push_cast
    rfl
  have hre : ∀ τ : E →+* ℂ, (τ (1 + (M : E) * ((K : E) * w))).re = 1 + (M : ℝ) * K * (τ w).re := by
    intro τ
    simp
    ring
  refine ⟨1 + (M : 𝓞 E) * ((K : 𝓞 E) * wO), ?_, ?_, ?_, (K : 𝓞 E) * wO, rfl⟩
  · rw [hcoe]
    simp [hwdef, add_comm]
  · rw [hcoe, hre]
    linarith
  · intro τ hτ
    rw [hcoe, hre]
    have := hpos τ hτ
    have : 0 ≤ (M : ℝ) * K * (τ w).re := by positivity
    linarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma hensel_root (p : ℕ) [Fact p.Prime] (tr nm r : ℤ) (hd : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (p : ℤ) ∣ r ^ 2 - tr * r + nm) :
    ∃ ρ : ℤ_[p], ρ ^ 2 - (tr : ℤ_[p]) * ρ + (nm : ℤ_[p]) = 0 := by
  have hF1 : ¬ (p : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hd
    have h2 : (p : ℤ) ∣ (2 * r - tr) ^ 2 := dvd_pow h two_ne_zero
    have h3 : (p : ℤ) ∣ 4 * (r ^ 2 - tr * r + nm) := dvd_mul_of_dvd_right hr 4
    have h4 := dvd_sub h2 h3
    have : (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [this] at h4
  set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C tr * Polynomial.X + Polynomial.C nm with hFdef
  have hval : Polynomial.aeval (r : ℤ_[p]) F = ((r ^ 2 - tr * r + nm : ℤ) : ℤ_[p]) := by
    simp [hFdef]
  have hder : Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F) = ((2 * r - tr : ℤ) : ℤ_[p]) := by
    simp [hFdef]
    left
    exact map_ofNat _ 2
  have hn1 : ‖Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F)‖ = 1 := by
    rw [hder]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    push_neg at hlt
    exact hF1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt)
  have hn0 : ‖Polynomial.aeval (r : ℤ_[p]) F‖ < 1 := by
    rw [hval]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hr
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (r : ℤ_[p])) (by rw [hn1]; simpa using hn0)
  refine ⟨z, ?_⟩
  simpa [hFdef] using hz

theorem UpperTheory.Gal.W2.Seed.pUEx :
    UEx := by
  intro E _ _ _ A p _ hsplit Kq hω hspan τ
  unfold Arith.SplitK at hsplit
  obtain ⟨hd, r, hr⟩ := hsplit
  obtain ⟨ρ, hρ⟩ := hensel_root p A.tr A.nm r hd hr
  set ι := algebraMap ℚ_[p] (PadicAlgCl p) with hι
  have hinj : Function.Injective ι := ι.injective
  set w := τ ((A.ω : 𝓞 E) : E) with hwdef
  have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]
    ring
  have h1 : ((A.ω : E)) ^ 2 - (A.tr : E) * (A.ω : E) + (A.nm : E) = 0 := by
    have := congrArg (fun x : 𝓞 E => (x : E)) h0
    simpa using this
  have hw : w ^ 2 - (A.tr : PadicAlgCl p) * w + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg τ h1
    simpa [hwdef] using this
  have hc : ι (ρ : ℚ_[p]) ^ 2 - (A.tr : PadicAlgCl p) * ι (ρ : ℚ_[p]) + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg (fun t : ℤ_[p] => ι (t : ℚ_[p])) hρ
    simpa using this
  have hprod : (w - ι (ρ : ℚ_[p])) * (w - ((A.tr : PadicAlgCl p) - ι (ρ : ℚ_[p]))) = 0 := by
    linear_combination hw - hc
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℤ_[p], w = ι (ρ₀ : ℚ_[p]) := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact ⟨ρ, sub_eq_zero.1 h⟩
    · refine ⟨(A.tr : ℤ_[p]) - ρ, ?_⟩
      rw [sub_eq_zero.1 h]
      simp
  have hex : ∀ x : Kq, ∃ q : ℚ_[p], ι q = τ (x : E) := by
    intro x
    obtain ⟨a, b, hab⟩ := hspan x x.2
    refine ⟨(a : ℚ_[p]) + (b : ℚ_[p]) * (ρ₀ : ℚ_[p]), ?_⟩
    rw [hab]
    simp [← hρ₀, hwdef]
  choose f hf using hex
  let u : Kq →+* ℚ_[p] :=
    { toFun := f
      map_one' := hinj (by rw [hf]; simp)
      map_mul' := fun x y => hinj (by rw [hf, map_mul, hf, hf]; simp)
      map_zero' := hinj (by rw [hf]; simp)
      map_add' := fun x y => hinj (by rw [hf, map_add, hf, hf]; simp) }
  refine ⟨u, ρ₀, ?_, ?_⟩
  · unfold LiesOver
    intro x
    exact (hf x).symm
  · apply hinj
    show ι (f ⟨_, hω⟩) = _
    rw [hf, ← hρ₀]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
section
noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E]

def ev1 (σ : E →+* ℂ) : ℝ ⊗[ℚ] E →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ) σ.toRatAlgHom (fun _ _ => Commute.all _ _)

def evM {n : ℕ} (σ : E →+* ℂ) : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (σ.mapMatrix).toRatAlgHom
    (fun x _ => Algebra.commute_algebraMap_left x _)

theorem realTensorEvalAlgHom_tmul (σ : E →+* ℂ) (r : ℝ) (x : E) : ev1 σ (r ⊗ₜ x) = r • σ x := by
  simp [ev1, Algebra.ofId_apply, Algebra.smul_def]

theorem evM_tmul {n : ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Matrix (Fin n) (Fin n) E) :
    evM σ (r ⊗ₜ x) = r • x.map σ := by
  unfold evM
  refine (Algebra.TensorProduct.lift_tmul _ _ _ r x).trans ?_
  rw [Algebra.smul_def]
  rfl

theorem evM_conj {n : ℕ} (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    evM (ComplexEmbedding.conjugate σ) z = (evM σ z).map (starRingEnd ℂ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [evM_tmul, evM_tmul]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]
  | add a b ha hb => rw [map_add, ha, hb, map_add, Matrix.map_add _ (map_add _)]

def Th {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V] (β : V →ₗ[ℚ] (Fin n → E)) :
    ℝ ⊗[ℚ] V →ₗ[ℝ] (K × Fin n → ℂ) :=
  LinearMap.liftBaseChange ℝ
    { toFun := fun w k => f k.1 (β w k.2)
      map_add' := fun a b => by ext k; simp
      map_smul' := fun q a => by ext k; simp [map_rat_smul] }

theorem Th_tmul {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (r : ℝ) (w : V) (k : K × Fin n) :
    Th f β (r ⊗ₜ w) k = r • f k.1 (β w k.2) := by
  simp [Th]

private theorem th_actOn_tmul_eq_evM_mulVec {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (r s : ℝ) (m : Matrix (Fin n) (Fin n) E) (w : V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w)) (τ, i) = (evM (f τ) (r ⊗ₜ m) *ᵥ fun j => Th f β (s ⊗ₜ w) (τ, j)) i := by
  have hl : actOn rep ℝ (r ⊗ₜ m) = algebraMap ℝ _ r * (Module.End.baseChangeHom ℚ ℝ V) (rep m) := by
    unfold actOn
    exact Algebra.TensorProduct.lift_tmul _ _ _ r m
  have ha : actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w) = (r * s) ⊗ₜ rep m w := by
    rw [hl, Module.End.mul_apply, Module.algebraMap_end_apply]
    show r • LinearMap.baseChange ℝ (rep m) (s ⊗ₜ w) = _
    rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rw [ha, Th_tmul, evM_tmul, hβ]
  simp only [Th_tmul]
  rw [RingHom.map_mulVec]
  simp [Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem Th_act {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (y : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (x : ℝ ⊗[ℚ] V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ y x) (τ, i) = (evM (f τ) y *ᵥ fun j => Th f β x (τ, j)) i := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    induction x using TensorProduct.induction_on with
    | zero =>
      simp
      exact (congrFun (Matrix.mulVec_zero _) i).symm
    | tmul s w => exact th_actOn_tmul_eq_evM_mulVec f β rep hβ r s m w τ i
    | add a b ha hb =>
      rw [map_add, map_add, Pi.add_apply, ha, hb]
      have : (fun j => Th f β (a + b) (τ, j)) = (fun j => Th f β a (τ, j)) + (fun j => Th f β b (τ, j)) := by
        ext j
        simp
      rw [this, Matrix.mulVec_add, Pi.add_apply]
  | add c d hc hd =>
    rw [map_add, LinearMap.add_apply, map_add, Pi.add_apply, hc, hd, map_add, Matrix.add_mulVec, Pi.add_apply]

variable [IsCMField E]

theorem evM_star {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (hH : (H.map (IsCMField.complexConj E : E →+* E))ᵀ = H)
    (hdet : H.det ≠ 0) (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    gramAt H σ * evM σ (starT (hermStar H hdet) ℝ z).unop = (evM σ z)ᴴ * gramAt H σ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) E,
      (M.map (IsCMField.complexConj E : E →+* E)).map σ = (M.map σ).map (starRingEnd ℂ) := by
    intro M
    ext i j
    simp [IsCMField.complexEmbedding_complexConj]
  have hHc : (H.map (IsCMField.complexConj E : E →+* E)).map σ = gramAt H σ := by
    have h1 := congrArg Matrix.transpose hH
    rw [Matrix.transpose_transpose] at h1
    rw [h1, gramAt, Matrix.transpose_map]
  have hu : IsUnit (H.map (IsCMField.complexConj E : E →+* E)).det := by
    rw [show (H.map (IsCMField.complexConj E : E →+* E)).det = (IsCMField.complexConj E : E →+* E) H.det from
      (RingHom.map_det _ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  have hG : IsUnit (gramAt H σ).det := by
    rw [gramAt, Matrix.det_transpose, show (H.map σ).det = σ H.det from (RingHom.map_det σ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, hermStar_apply, evM_tmul, evM_tmul, Matrix.map_mul, Matrix.map_mul,
      map_nonsingInv σ hu, hHc, Matrix.transpose_map, hc x, Matrix.conjTranspose_smul]
    have hx : ((x.map σ).map (starRingEnd ℂ))ᵀ = (x.map σ)ᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [hx, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mul, star_trivial, Matrix.smul_mul]
  | add a b ha hb =>
    rw [map_add, MulOpposite.unop_add, map_add, map_add, Matrix.mul_add, ha, hb,
      Matrix.conjTranspose_add, Matrix.add_mul]

theorem term_pos (D h z : ℂ) (hD : D.re = 0) (hD' : D.im < 0) (hi : h.im = 0) (hr : h.re ≠ 0) :
    0 ≤ (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re ∧
    (z ≠ 0 → 0 < (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re) := by
  have hz : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have e : D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z =
      D * h * (if 0 < h.re then Complex.I else -Complex.I) * (Complex.normSq z : ℂ) := by
    rw [← hz]
    ring
  rw [e]
  have hc : (D * h * (if 0 < h.re then Complex.I else -Complex.I)).re = |D.im| * |h.re| := by
    split_ifs with hp
    · simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_pos hp]
      ring
    · have hn : h.re < 0 := lt_of_le_of_ne (not_lt.mp hp) hr
      simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_neg hn]
      ring
  have hpos : 0 < |D.im| * |h.re| := mul_pos (abs_pos.mpr hD'.ne) (abs_pos.mpr hr)
  rw [Complex.re_mul_ofReal, hc]
  refine ⟨mul_nonneg hpos.le (Complex.normSq_nonneg z), fun hz0 => ?_⟩
  exact mul_pos hpos (Complex.normSq_pos.mpr hz0)

end UpperTheory.Gal.W2.Seed.Ori
end
end

