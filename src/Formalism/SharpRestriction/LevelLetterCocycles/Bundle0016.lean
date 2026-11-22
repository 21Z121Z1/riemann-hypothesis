import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeMapMemLattice
import Formalism.SharpRestriction.LevelLetterCocycles.Imports
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0002

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGCut

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lemG_sig (l H : ℕ) : ℕ := ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def LemGPair [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (x la : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∃ (x la : W.DD T₂) (hP : LemGPair W T₂ b S η i x la),
        W.cmp T₂ ⟨x, hP.1⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

def LemGB [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∃ E : ℕ, (E : ℝ) ≤ (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) +
        lam PD.p (hpar n b S + η) ∧
      ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
        ∃ y ∈ W.N T₁, Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i y ∧ W.map F y = ((PD.p : O) ^ E) • x

theorem lemG_ceil_eq (l H E h b : ℕ) :
    (⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ)⌉ : ℤ) =
      (E : ℤ) + ((lemG_sig l H : ℤ) + (h : ℤ) - (b : ℤ)) := by
  have hs : Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H = ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2]
    push_cast
    ring
  have h0 : 0 ≤ ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc : ((lemG_sig l H : ℕ) : ℤ) = ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉ := by
    unfold lemG_sig
    exact Int.natCast_ceil_eq_ceil h0
  rw [show (E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ) =
      (((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1) + (((E : ℤ) + h - b : ℤ) : ℝ) by
        rw [hs]; push_cast; ring,
    Int.ceil_add_intCast, ← hc]
  ring

theorem lemmaGs_of_lemGAB [NeZero n] (W : LocWach PD LL O v n) (hA : LemGA W) (hB : LemGB W) :
    LemmaGs W := by
  intro d T₁ T₂ F b S η m hset i hi
  obtain ⟨E, hEb, hEx⟩ := hB d T₁ T₂ F b S η m hset i hi
  refine ⟨E, hEb, ?_⟩
  rintro _ ⟨_, ⟨y, hy, hyD, rfl⟩, rfl⟩ hfil
  obtain ⟨x, la, hP, hcmp⟩ := hA d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨y1, hy1N, hy1D, hmap⟩ := hEx x la hP
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hset.2.2.2.2.1
    haveI : NeZero PD.p := ⟨by have := hset.2.1; omega⟩
    exact hζ.neZero'.out
  have hnat : ((PD.p : ℕ) : O) ^ E • x = (PD.p ^ E : ℕ) • x := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hx' : W.map F y1 ∈ W.N T₂ := by
    rw [hmap, hnat]
    exact nsmul_mem hP.1 _
  refine ⟨y1, hy1N, hx', hy1D, ?_⟩
  rw [lemG_ceil_eq, zpow_add₀ hp0, mul_smul, ← hcmp]
  have hsub : (⟨W.map F y1, hx'⟩ : W.N T₂) = (PD.p ^ E : ℕ) • (⟨x, hP.1⟩ : W.N T₂) :=
    Subtype.ext (by show W.map F y1 = (PD.p ^ E : ℕ) • x; rw [hmap, hnat])
  rw [hsub, map_nsmul, zpow_natCast, ← Nat.cast_smul_eq_nsmul LL, Nat.cast_pow]

def LemGLa [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (y la : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T (i - 2) 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η)) y la ∧
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i la ∧
    Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA_la [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ y : W.DD T₂, y ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∃ la : W.DD T₂, LemGLa W T₂ b S η i y la

def GammaActionLemma [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
        ∃ x : W.DD T₂, x ∈ W.N T₂ ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x ∧
          Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la

def LemGA_0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
      ∀ (x : W.DD T₂) (hx : x ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x →
        Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la →
        W.cmp T₂ ⟨x, hx⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

theorem lemGA_of_pieces [NeZero n] (W : LocWach PD LL O v n) (hla : LemGA_la W) (hx : GammaActionLemma W)
    (h0 : LemGA_0 W) : LemGA W := by
  intro d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨la, hla⟩ := hla d T₁ T₂ F b S η m hset i hi y hy hyD
  obtain ⟨x, hxN, hxD, hxeq⟩ := hx d T₁ T₂ F b S η m hset i hi y hy hyD hfil la hla
  exact ⟨x, la, ⟨hxN, hxD, hxeq, hla.2.2.2⟩,
    h0 d T₁ T₂ F b S η m hset i hi y hy hyD la hla x hxN hxD hxeq⟩

end LemGCut

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LiftFOf
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem lc_pow (I : BaseId W) (e : ℕ) :
    I.Bs.lc ^ e = PowerSeries.C (((PD.p : ℕ) : O) ^ e) := by
  unfold Formalism.ExponentWindows.E.Base.lc
  rw [I.ℓ_eq, map_pow]

theorem map_mem_Z1DΔ (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) ∈ W.wachCocyclesDelta T₂ := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  show (W.map F x, W.map F y) ∈ W.wachCocyclesDelta T₂
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Formalism.BasicNotions.herrCocycles, Submodule.mem_inf,
    LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply, LinearMap.prodMap_apply] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, fun d hd => ?_⟩
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, ← map_neg, ← map_add, h1, map_zero]
  · have h3 := h2 d hd
    rw [← W.map_γ, ← W.map_γ]
    simp only [Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at h3 ⊢
    exact ⟨by rw [h3.1], by rw [h3.2]⟩

private theorem inv_lemma' {T : LocLat G Qp LL O} (w : ↥(W.wachCocyclesDelta T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (w : W.DD T × W.DD T).1 = (w : W.DD T × W.DD T).1 ∧
      W.γD T δ (w : W.DD T × W.DD T).2 = (w : W.DD T × W.DD T).2 := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.prodMap_apply,
    Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at hw
  exact hw.2 δ hδ

theorem liftF_of {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hs : W.s = 1) (hp : PD.p ≠ 2) (herr : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T₂)
    (nat : W.ClKNat) (e : ℕ)
    (key : ∀ κ ∈ Zf C₂, ∃ κ₁ ∈ Zf C₁,
      (latOf C₂).IsCobound (I.Bs.lc ^ e • κ.1 - fun i => (latHomOf h).f (κ₁.1 i))
        (I.Bs.lc ^ e • κ.2 - fun i => (latHomOf h).f (κ₁.2 i))) :
    F.LiftF PD e := by
  intro c hc
  have hcZ : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 hc).1
  have hsurj : Function.Surjective (W.clK T₂) := (herr hs hp).1
  have hker : ∀ w : ↥(W.wachCocyclesDelta T₂), W.clK T₂ w = 0 ↔ ∃ m : W.DD T₂, Formalism.MainNotions.DeltaInvariantLattices.DInv W T₂ m ∧
      (w : W.DD T₂ × W.DD T₂) = (W.φD T₂ m - m, W.γD T₂ W.gamK m - m) := (herr hs hp).2
  obtain ⟨w, hw⟩ : ∃ w : ↥(W.wachCocyclesDelta T₂),
      W.clK T₂ w = Submodule.mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype) ⟨c, hcZ⟩ :=
    hsurj (Submodule.mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype) ⟨c, hcZ⟩)
  obtain ⟨y1, hy1⟩ := tot_surj C₂ (w : W.DD T₂ × W.DD T₂).1 (fun δ hδ => (inv_lemma' w δ hδ).1)
  obtain ⟨y2, hy2⟩ := tot_surj C₂ (w : W.DD T₂ × W.DD T₂).2 (fun δ hδ => (inv_lemma' w δ hδ).2)
  have hκ : ((y1, y2) : (ZMod n → C₂.V) × (ZMod n → C₂.V)) ∈ Zf C₂ := by
    show totP C₂ (y1, y2) ∈ ZfD W T₂
    have ht : totP C₂ (y1, y2) = (w : W.DD T₂ × W.DD T₂) := Prod.ext hy1 hy2
    rw [ht]
    refine ⟨w, ?_, rfl⟩
    show W.clK T₂ w ∈ latticeFiniteCohomology PD T₂.L
    rw [hw]
    exact ⟨⟨c, hcZ⟩, hc, rfl⟩
  obtain ⟨κ₁, hκ₁, hcob⟩ := key (y1, y2) hκ
  obtain ⟨m, hm1, hm2⟩ := hcob
  obtain ⟨w₁, hw₁, hw₁e⟩ : ∃ w₁, w₁ ∈ (latticeFiniteCohomology PD T₁.L).comap (W.clK T₁) ∧
      (W.wachCocyclesDelta T₁).subtype w₁ = totP C₁ κ₁ := hκ₁
  obtain ⟨z₁, hz₁, hz₁e⟩ : ∃ z₁, z₁ ∈ (latticeFiniteCocycles PD T₁.L).comap (latticeCocycles T₁.L).subtype ∧
      Submodule.mkQ ((latticeCoboundaries T₁.L).comap (latticeCocycles T₁.L).subtype) z₁ = W.clK T₁ w₁ := hw₁
  have hw1e1 : tot C₁ κ₁.1 = (w₁ : W.DD T₁ × W.DD T₁).1 := (congrArg Prod.fst hw₁e).symm
  have hw1e2 : tot C₁ κ₁.2 = (w₁ : W.DD T₁ × W.DD T₁).2 := (congrArg Prod.snd hw₁e).symm
  have e1 : (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).1 - W.map F (w₁ : W.DD T₁ × W.DD T₁).1
      = W.φD T₂ (tot C₂ m) - tot C₂ m := by
    have h1 : I.Bs.lc ^ e • y1 - (fun i => (latHomOf h).f (κ₁.1 i)) = (latOf C₂).dφ m := hm1
    have h1' := congrArg (tot C₂) h1
    rw [tot_sub, tot_smul, tot_map h κ₁.1, tot_dφ, lc_pow I e, BaseId.d_C, algebraMap_smul, hy1,
      hw1e1] at h1'
    exact h1'
  have e2 : (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).2 - W.map F (w₁ : W.DD T₁ × W.DD T₁).2
      = W.γD T₂ W.gamK (tot C₂ m) - tot C₂ m := by
    have h2 : I.Bs.lc ^ e • y2 - (fun i => (latHomOf h).f (κ₁.2 i)) = (latOf C₂).dγ m := hm2
    have h2' := congrArg (tot C₂) h2
    rw [tot_sub, tot_smul, tot_map h κ₁.2, tot_dγ, lc_pow I e, BaseId.d_C, algebraMap_smul, hy2,
      hw1e2] at h2'
    exact h2'
  obtain ⟨w₁', hw₁'⟩ : ∃ w' : ↥(W.wachCocyclesDelta T₂), (w' : W.DD T₂ × W.DD T₂) =
      (W.map F (w₁ : W.DD T₁ × W.DD T₁).1, W.map F (w₁ : W.DD T₁ × W.DD T₁).2) :=
    ⟨⟨_, map_mem_Z1DΔ F w₁⟩, rfl⟩
  have hnat := nat F w₁ w₁' hw₁'
  have hD : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - w₁') = 0 := by
    rw [hker]
    refine ⟨tot C₂ m, fun δ hδ => tot_Δ C₂ m δ hδ, Prod.ext ?_ ?_⟩
    · show (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).1 - (w₁' : W.DD T₂ × W.DD T₂).1 = _
      rw [hw₁']
      exact e1
    · show (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).2 - (w₁' : W.DD T₂ × W.DD T₂).2 = _
      rw [hw₁']
      exact e2
  have hD' : (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w = W.clK T₂ w₁' := by
    have h0 : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w) - W.clK T₂ w₁' = 0 :=
      (map_sub (W.clK T₂) _ _).symm.trans hD
    have hs : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w) = (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w :=
      map_smul (W.clK T₂) _ _
    rw [← hs]
    exact sub_eq_zero.1 h0
  rw [hw, ← hnat, ← hz₁e, ← map_smul] at hD'
  simp only [Formalism.WeaklyAdmissibleFiltrations.LatHom.H1map, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.Quotient.eq] at hD'
  erw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hD'
  have hB : (((PD.p : ℕ) : O) ^ e) • c - F.post (z₁ : G → _) ∈ latticeCoboundaries T₂.L := hD'
  refine Submodule.mem_sup.2 ⟨F.post (z₁ : G → _), ⟨(z₁ : G → _), hz₁, rfl⟩, _, hB, ?_⟩
  abel

end Formalism.MainNotions.WachCoordinates.Br
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Crys

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def matOf {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) :
    G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp ρ

theorem matOf_equiv {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) (x : V) :
    b.equivFun (ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL ≃ₐ[LL] _).toAlgHom.toRingHom.toMonoidHom.comp
        (matOf b ρ)) g (b.equivFun x) := by
  simp only [matOf, MonoidHom.coe_comp, Function.comp_apply, Module.Basis.equivFun_apply]
  change ⇑(b.repr ((ρ g) x)) = (Matrix.toLinAlgEquiv' (LinearMap.toMatrix b b (ρ g))) ⇑(b.repr x)
  rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix_mulVec_repr]

theorem isCrys_bρ {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V)
    (h : IsCrys PD ρ) : IsCrys PD (bρ LL' ρ) := by
  have h1 := Formalism.MainNotions.N.K.Norm.isCrys_congr PD b.equivFun (matOf_equiv b ρ) h
  have h2 := coefficient_crystal_generation PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) h1
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  refine Formalism.MainNotions.N.K.Norm.isCrys_congr PD b'.equivFun.symm (fun g y => ?_) h2
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  apply b'.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  have e1 := matOf_equiv b' (bρ LL' ρ) g (b'.equivFun.symm y)
  rw [LinearEquiv.apply_symm_apply] at e1
  rw [e1]
  simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
  rfl

end Crys

section LocC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem crysLat_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) (hT : Formalism.MainNotions.WachCoordinates.CrysLat PD T) :
    Formalism.MainNotions.WachCoordinates.CrysLat PD (bLoc (O' := O') hc hO' T) :=
  ⟨(bLoc (O' := O') hc hO' T).fdim, (bLoc (O' := O') hc hO' T).mtop, (bLoc (O' := O') hc hO' T).cont,
    isCrys_bρ PD (Module.finBasis LL T.V) T.ρ hT.2.2.2⟩

theorem finrank_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) :
    Module.finrank LL' (bLoc (O' := O') hc hO' T).V = Module.finrank LL T.V :=
  Module.finrank_baseChange

end LocC

section Jmp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem isJumpV_bρ (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    IsJumpV PD (bρ LL' ρ) ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a ↔ IsJumpV PD ρ τ a := by
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b.equivFun (matOf_equiv b ρ) τ a
  have e2 := hJ PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) τ a
  have he' : ∀ g x, b'.equivFun (bρ LL' ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL' ≃ₐ[LL'] _).toAlgHom.toRingHom.toMonoidHom.comp
        ((IsScalarTower.toAlgHom Qp LL LL').mapMatrix.toRingHom.toMonoidHom.comp (matOf b ρ))) g
        (b'.equivFun x) := by
    intro g x
    rw [matOf_equiv b' (bρ LL' ρ) g x]
    simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
    rfl
  have e3 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b'.equivFun he' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a
  rw [e3, ← e2, ← e1]

end Jmp

section Assemble

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_of (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen)
    (hL : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ e, (bHom (O' := O') hc hO' F).LiftF PD e → F.LiftF PD e)
    (hC : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ x, Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD (bHom (O' := O') hc hO' F) x → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F x) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') := by
  intro T₁ T₂ F h₁ h₂ hF
  refine ⟨bLoc hc hO' T₁, bLoc hc hO' T₂, bHom hc hO' F, crysLat_b PD hc hO' T₁ h₁,
    crysLat_b PD hc hO' T₂ h₂, bHom_onto hc hO' F hF, fun τ a => ⟨?_, ?_⟩, finrank_b hc hO' T₂,
    hL T₁ T₂ F h₁ h₂ hF, hC T₁ T₂ F h₁ h₂ hF⟩
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₁.V) T₁.ρ τ a
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₂.V) T₂.ρ τ a

end Assemble

end Formalism.MainNotions.UnusedSlot80.BCW
end
end

