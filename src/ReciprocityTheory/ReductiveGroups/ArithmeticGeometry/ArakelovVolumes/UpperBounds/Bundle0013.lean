import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Reading (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ) where

  Rg : Subring (A c)
  w_mem : ∀ j, d.w j c ∈ Rg
  rd : Rg →+* (Frame X.Ψ r → ℂ)

  WE : AddSubgroup WT
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ r

  Gen : Set (Frame X.Ψ r)
  Gen_sub : Gen ⊆ X.dom
  Gen_dense : X.dom ⊆ closure Gen
  pt : Frame X.Ψ r → (Ω c →+* ℂ)
  pt_mem : ∀ x ∈ Gen, pt x ∈ PT (Ω := Ω c) sg
  pt_onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x ∈ Gen, pt x = P

  w_nz : ∀ x ∈ X.dom, ∃ j, rd ⟨d.w j c, w_mem j⟩ x ≠ 0
  sec : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → X.IsSec (wt ⟨G, hG⟩) (rd ⟨f, hf⟩)
  inj : ∀ G, ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → (∀ x ∈ X.dom, rd ⟨f, hf⟩ x = 0) → f = 0
  norm : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → ∀ x ∈ Gen,
    X.pnorm (wt ⟨G, hG⟩) (rd ⟨f, hf⟩) x = d.nrm c G f (pt x)
  ratio_rd : ∀ G, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 → ∀ x ∈ Gen,
    rd ⟨f, hf⟩ x = pt x (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x

  Gen_inv : ∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x
  orbit_inj : ∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x' = lact γ (rmul x b)

  Gen_max : ∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Ω c) sg,
    (∀ G ∈ WE, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 →
      rd ⟨f, hf⟩ x = P (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P

  bir : ∀ a : Ω c, ∃ (G : WT) (f p : A c), f ∈ Rg ∧ p ∈ Rg ∧ f ∈ 𝒜 c G ∧ p ∈ 𝒜 c G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin K (Set.range fun j => d.w j c) ∧ a = ratio (Ω := Ω c) f p

  coordAt : ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    rd ⟨d.w j0 c, w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      rd ⟨d.w (jj k) c, w_mem (jj k)⟩ (cpt X x z) / rd ⟨d.w j0 c, w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0

structure BeData (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) where
  k : ℕ
  be : A c
  be_mem : be ∈ R.Rg
  be_in : be ∈ 𝒜 c (k • d.wL)
  be_ne : be ≠ 0
  w_pos : ∀ x ∈ X.dom, 0 < ∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2
  be1 : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (R.wt ⟨k • d.wL, R.WE.nsmul_mem R.wL_mem k⟩) (R.rd ⟨be, be_mem⟩) x ≤
    C * (∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2) ^ ((k : ℝ) / 2)
  be2 : ∀ δ : ℝ, 0 < δ → ∃ Cs : Set (Frame X.Ψ r), IsCompact Cs ∧ Cs ⊆ X.dom ∧
    ∀ x ∈ X.dom, δ * (∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2) ^ ((k : ℝ) / 2) ≤
      X.pnorm (R.wt ⟨k • d.wL, R.WE.nsmul_mem R.wL_mem k⟩) (R.rd ⟨be, be_mem⟩) x →
      ∃ y ∈ Cs, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul y b)

def SgGeneric {D N : ℕ} (sg : K →+* ℂ) (t : TVar D N → ℂ) : Prop :=
  ∀ Q : MvPolynomial (TVar D N) K, Q ≠ 0 → MvPolynomial.eval₂ sg t Q ≠ 0

def FlatOfAlgStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ) (Bd : BeData (𝒜 := 𝒜) d c R),
    Xa.L = R.wt ⟨d.wL, R.wL_mem⟩ → (∀ k, Xa.w k = R.rd ⟨d.w (e k) c, R.w_mem _⟩) → SgGeneric sg t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    NormStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    d.S1 → Algebra.IsSeparable (d.KT c) (OmS (Ω c) d.D d.N) → PropDisc X →
    ∃ Fl : FlatM X Xa,
      (∀ x, Fl.w0 x = ∑ j, t (0, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x) ∧
      ∀ i x, Fl.s i x = ∑ j, t ((Fin.cast hD i).succ, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x

def w0R (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) (t : TVar d.D d.N → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ j, t (0, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x

def sR (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) (t : TVar d.D d.N → ℂ) (hD : nd X = d.D) (i : Fin (nd X))
    (x : Frame X.Ψ r) : ℂ :=
  ∑ j, t ((Fin.cast hD i).succ, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x

def FlatHyp (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ) : Prop :=
  d.AxW 𝒜 ∧ Xa.L = R.wt ⟨d.wL, R.wL_mem⟩ ∧ (∀ k, Xa.w k = R.rd ⟨d.w (e k) c, R.w_mem _⟩) ∧ SgGeneric sg t ∧
    d.S1 ∧ Algebra.IsSeparable (d.KT c) (OmS (Ω c) d.D d.N) ∧ PropDisc X

def SPointsStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ R.Gen) ∧
      (∀ x ∈ X.dom, (∀ i, sR d c R t hD i x = 0) ↔
        ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      (∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j') ∧
      ∀ j, w0R d c R t (xs j) ≠ 0

def SCoordStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    ∀ x ∈ R.Gen, (∀ i, sR d c R t hD i x = 0) → w0R d c R t x ≠ 0 →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun i =>
        sR d c R t hD i (cpt X x z) / w0R d c R t (cpt X x z) : V (nd X))) 0).det ≠ 0

def WLeStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    ∃ Kc : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
      Kc * (X.pnorm Xa.L (w0R d c R t) x ^ 2 + ∑ i, X.pnorm Xa.L (sR d c R t hD i) x ^ 2)

def WLeSStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    NormStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) → PropDisc X →
    BeData (𝒜 := 𝒜) d c R →
    ∀ U : Set (Frame X.Ψ r), IsOpen U →
      (∀ x ∈ X.dom, (∀ i, sR d c R t hD i x = 0) → x ∈ U) →
      (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
      ∃ Kc : ℝ, ∀ x ∈ X.dom, x ∉ U →
        ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ Kc * ∑ i, X.pnorm Xa.L (sR d c R t hD i) x ^ 2

def SSgtLinStatement : Prop :=
  ∀ (r : ℕ) (X : FD.Data E r) (la : Wt X.Ψ r) (c : ℝ) {ι' : Type} (s : Finset ι') (a : ι' → ℂ)
    (P : ι' → Frame X.Ψ r → ℂ), (∀ i ∈ s, P i ∈ X.SSgt la c) →
    (fun x => ∑ i ∈ s, a i * P i x) ∈ X.SSgt la c

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem mulO {f g : V n → ℂ} {a b c : ℕ} (hf : f =O[𝓝 0] fun z => ‖z‖ ^ a)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ b) (h : a + b = c) :
    (fun z => f z * g z) =O[𝓝 0] fun z => ‖z‖ ^ c := by
  subst h
  exact (hf.mul hg).congr_right fun z => (pow_add _ _ _).symm

theorem pow_sub_pow {u v : V n → ℂ} (hu : u =O[𝓝 0] fun z => ‖z‖) (hv : v =O[𝓝 0] fun z => ‖z‖)
    (huv : (fun z => u z - v z) =O[𝓝 0] fun z => ‖z‖ ^ 2) (e : ℕ) :
    (fun z => u z ^ e - v z ^ e) =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  rcases e with _ | e
  · simp only [pow_zero, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (0 + 1)) (𝓝 (0 : V n))
  · have hs : (fun z : V n => ∑ i ∈ Finset.range (e + 1), u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
        fun z : V n => ‖z‖ ^ e := by
      have hterm : ∀ i ∈ Finset.range (e + 1), (fun z : V n => u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
          fun z : V n => ‖z‖ ^ e := by
        intro i hi
        have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ((hu.pow i).mul (hv.pow (e + 1 - 1 - i))).congr_right fun z => ?_
        rw [← pow_add]
        congr 1
        omega
      exact (Asymptotics.IsBigO.sum hterm).congr_left fun z => Finset.sum_apply z _ _
    refine ((hs.mul huv).congr_left fun z => ?_).congr_right fun z => ?_
    · exact (Commute.all (u z) (v z)).geom_sum₂_mul (e + 1)
    · ring

theorem prod_pow_O {ι : Type*} (s : Finset ι) (u : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) :
    (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Asymptotics.isBigO_const_const (1 : ℂ) one_ne_zero _
  · intro a s ha ih
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mulO ((hu a).pow (e a)) ih rfl

theorem prod_pow_sub {ι : Type*} (s : Finset ι) (u v : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) (hv : ∀ i, v i =O[𝓝 0] fun z => ‖z‖)
    (huv : ∀ i, (fun z => u i z - v i z) =O[𝓝 0] fun z => ‖z‖ ^ 2) :
    (fun z => ∏ i ∈ s, u i z ^ e i - ∏ i ∈ s, v i z ^ e i) =O[𝓝 0]
      fun z => ‖z‖ ^ (∑ i ∈ s, e i + 1) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (∑ i ∈ (∅ : Finset ι), e i + 1)) (𝓝 (0 : V n))
  · intro a s ha ih
    have hc : e a + (∑ i ∈ s, e i + 1) = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have hc' : (e a + 1) + ∑ i ∈ s, e i = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have h1 := mulO ((hu a).pow (e a)) ih hc
    have h2 := mulO (pow_sub_pow (hu a) (hv a) (huv a) (e a)) (prod_pow_O s v e hv) hc'
    refine (h1.add h2).congr_left fun z => ?_
    simp only [Finset.prod_insert ha]
    ring

theorem taylor2 {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g z - g 0 - fderiv ℂ g 0 z) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hg
  have h := hp.isBigO_sub_partialSum_pow 2
  rw [hp.hasFDerivAt.fderiv]
  refine h.congr_left fun z => ?_
  have e1 : (p 1 fun _ => z) = p 1 ![z] := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, e1]
  try ring

theorem lower_of_deriv {φ : V n → V n} (L : V n ≃L[ℂ] V n)
    (h : (fun z => φ z - L z) =o[𝓝 0] fun z => z) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 0, c * ‖z‖ ≤ ‖φ z‖ := by
  set K : ℝ := ‖(L.symm : V n →L[ℂ] V n)‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  filter_upwards [h.def (show (0 : ℝ) < 1 / (2 * K) by positivity)] with z hz
  have h1 : ‖z‖ ≤ K * ‖L z‖ := by
    calc ‖z‖ = ‖(L.symm : V n →L[ℂ] V n) (L z)‖ := by simp
      _ ≤ ‖(L.symm : V n →L[ℂ] V n)‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖L z‖ := by gcongr; linarith
  have h2 : ‖L z‖ ≤ ‖φ z‖ + ‖φ z - L z‖ := by
    calc ‖L z‖ = ‖φ z - (φ z - L z)‖ := by congr 1; abel
      _ ≤ ‖φ z‖ + ‖φ z - L z‖ := norm_sub_le _ _
  have h3 : ‖z‖ / K ≤ ‖L z‖ := by rw [div_le_iff₀ hKpos]; linarith
  have h4 : ‖z‖ / K = 2 * (1 / (2 * K) * ‖z‖) := by field_simp; try ring
  linarith

theorem vanS_int (hn : 1 ≤ n) {a : ℕ} {G : V n → ℂ} {S : Fin n → V n → ℂ}
    (hG : G =O[𝓝 0] fun z => ‖z‖ ^ a) {c : ℝ} (hc : 0 < c)
    (hS : ∀ᶠ z in 𝓝 0, c * ‖z‖ ^ 2 ≤ ∑ k, ‖S k z‖ ^ 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖G z‖ ^ 2 *
      (∑ k, ‖S k z‖ ^ 2) ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hCpos, hC⟩ := hG.exists_pos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hC.bound.and hS)
  refine ⟨ρ, hρ, ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  set K : ℝ := C ^ 2 * c ^ (-β) with hK
  have hKpos : 0 < K := by positivity
  have hfin : Module.finrank ℝ (V n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hgi : MeasureTheory.IntegrableOn (fun z : V n => K * ‖z‖ ^ (-(2 * (n : ℝ) - 1)))
      (Metric.ball 0 ρ) := by
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := K) (α := 2 * (n : ℝ) - 1) ?_ ?_ ?_ ?_
    · rw [hfin]; omega
    · rw [hfin]; push_cast; linarith
    · refine MeasureTheory.ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have hlt := (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (MeasureTheory.ae_of_all _ fun z => by positivity)).mp hgi.2
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae ?_) hlt
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball,
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (0 : V n)))] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0'
  obtain ⟨h1, h2⟩ := hball z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
  apply ENNReal.ofReal_le_ofReal
  have e1 : ‖G z‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ (2 * a) := by
    calc ‖G z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := by gcongr
      _ = C ^ 2 * ‖z‖ ^ (2 * a) := by ring
  have e2 : (∑ k, ‖S k z‖ ^ 2) ^ (-β) ≤ (c * ‖z‖ ^ 2) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have e3 : (c * ‖z‖ ^ 2) ^ (-β) = c ^ (-β) * ‖z‖ ^ (-2 * β) := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
    ring_nf
  have e4 : ‖z‖ ^ (2 * a) * ‖z‖ ^ (-2 * β) = ‖z‖ ^ (-(2 * (n : ℝ) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hzpos]
    congr 1
    rw [hβ]
    push_cast
    ring
  calc ‖G z‖ ^ 2 * (∑ k, ‖S k z‖ ^ 2) ^ (-β) ≤ (C ^ 2 * ‖z‖ ^ (2 * a)) * (c * ‖z‖ ^ 2) ^ (-β) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = K * ‖z‖ ^ (-(2 * (n : ℝ) - 1)) := by rw [e3, hK, ← e4]; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

