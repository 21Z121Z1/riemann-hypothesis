import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.TranslationFrames
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ColumnSectionIdeal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnSectionIdeal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Row (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

abbrev Pol (Dw : Datum H) {l : Level H} (c : Coeff l) (n : ℕ) : Type :=
  MvPolynomial (Letter (E →+* ℂ) Dw.mult n) c.F

def colExp {Dw : Datum H} {n : ℕ} (m : Letter (E →+* ℂ) Dw.mult n →₀ ℕ) (j : Fin n) : Row Dw → ℕ :=
  fun ρ => m ⟨ρ.1, ρ.2, j⟩

def intRing {l : Level H} (c : Coeff l) : Subring c.F := (algebraMap (𝓞 c.F) c.F).range

def HHset (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Pol Dw c n) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (fun τ => τ (H.rt : E) = H.rt0) (fun τ i => a (τ, i))

def Hset (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Pol Dw c n) :=
  HaO Dw.mult n c.F (intRing c) ComplexEmbedding.conjugate (fun τ => τ (H.rt : E) = H.rt0) (fun τ i => a (τ, i))

def HLat (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Submodule (𝓞 c.F) (Pol Dw c n) where
  carrier := Hset Dw c a n
  zero_mem' := ⟨⟨Submodule.zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩,
    fun _ => by simp⟩
  add_mem' := by
    classical
    rintro P Q ⟨⟨hP1, hP2, hP3⟩, hP4⟩ ⟨⟨hQ1, hQ2, hQ3⟩, hQ4⟩
    refine ⟨⟨Submodule.add_mem _ hP1 hQ1, fun σ i i' h t => ?_, fun m hm => ?_⟩, fun m => ?_⟩
    · rw [map_add, hP2 σ i i' h t, hQ2 σ i i' h t]
    · rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hP3 m h
      · exact hQ3 m h
    · rw [MvPolynomial.coeff_add]; exact Subring.add_mem _ (hP4 m) (hQ4 m)
  smul_mem' := by
    rintro r P ⟨⟨hP1, hP2, hP3⟩, hP4⟩
    have e : r • P = (algebraMap (𝓞 c.F) c.F r) • P := (algebraMap_smul _ r P).symm
    suffices hs : (algebraMap (𝓞 c.F) c.F r) • P ∈ Hset Dw c a n from
      (congrArg (fun Q => Q ∈ Hset Dw c a n) e).mpr hs
    refine ⟨⟨Submodule.smul_mem _ _ hP1, fun σ i i' h t => ?_, fun m hm => ?_⟩, fun m => ?_⟩
    · rw [map_smul, hP2 σ i i' h t]
    · exact hP3 m (MvPolynomial.support_smul hm)
    · rw [MvPolynomial.coeff_smul]; exact Subring.mul_mem _ ⟨r, rfl⟩ (hP4 m)

def admitted (l : Level H) (N : ℕ) : Prop := Odd N ∧ l.M ∣ N

open Classical in

def transIdeal (l : Level H) (N : ℕ) : Ideal (𝓞 E) :=
  ∏ 𝔓 ∈ (UniqueFactorizationMonoid.normalizedFactors l.Mb).toFinset,
    𝔓 ^ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 E)})).count 𝔓

variable {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def KilledBy (I : Ideal (𝓞 E)) (T : Over Xo.X) (z : T ⟶ Xo.univ.t.G) : Prop :=
  ∀ b ∈ I, z ≫ Xo.univ.t.act.act b = 1

def levelPt (T : Over Xo.X) (x : Dw.La) : T ⟶ Xo.univ.t.G := toUnit T ≫ Xo.univ.eta x

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ) : Type :=
  LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk y.x))

abbrev Jet : Type 1 :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ), SecAt Xo c y k → (Row Dw → ℕ) → S

variable {Xo c}

def pairBox (J : Jet Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ) {n : ℕ}
    (P : Pol Dw c n) (F : Fin n → SecAt Xo c y k) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ j, J S y k (F j) (colExp m j)

def IsColSec (N : ℕ) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (x : Dw.La)
    (F : SecAt Xo c y ((N : ℤ) ^ 2)) : Prop :=
  TranslationFrames.IsTranslPull Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo (transIdeal l N ^ 2))
    (levelPt Xo (Over.mk y.x) x) y.s F

def IsThValueAt (J : Jet Xo c) (N : ℕ) {n : ℕ} (x : Fin n → Dw.La) (P : Pol Dw c n)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  admitted l N ∧ ∃ F : Fin n → SecAt Xo c y ((N : ℤ) ^ 2), (∀ j, IsColSec N y (x j) (F j)) ∧
    v = algebraMap c.F S (((N : c.F)⁻¹) ^ P.totalDegree) * pairBox J y ((N : ℤ) ^ 2) P F

def IsThValue (J : Jet Xo c) {n : ℕ} (x : Fin n → Dw.La) (P : Pol Dw c n)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  IsThValueAt J l.M x P y v

def IsThRule (J : Jet Xo c) {n : ℕ} (x : Fin n → Dw.La) (P : Pol Dw c n) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), IsThValue J x P y (f p y)

def IsTh (J : Jet Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : Pol Dw c n)
    (f : Rul Xo c) : Prop :=
  P ∈ Hset Dw c a n ∧ IsThRule J x P f

def thGenOn (J : Jet Xo c) {n : ℕ} (B : Set (Pol Dw c n)) : Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La), ∃ P ∈ B, IsThRule J x P f}

def thGen (J : Jet Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La) (P : Pol Dw c n), IsTh J a n x P f}

def thAll (J : Jet Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  Submodule.span (𝓞 c.F) (thGen J a n)

def LatticeSt (Dw : Datum H) (c : Coeff l) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (HLat Dw c a n).FG ∧
    (Submodule.span c.F (Hset Dw c a n) : Set (Pol Dw c n)) = HHset Dw c a n

def TransIdealSt (Xo : Moduli Dw l) : Prop :=
  transIdeal l l.M = l.Mb ∧ ∀ N, admitted l N → ∀ (T : Over Xo.X) (x : Dw.La),
    KilledBy Xo (transIdeal l N) T (levelPt Xo T x)

def ColSecSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ N, admitted l N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (x : Dw.La),
    ∃! F, IsColSec N y x F

def FreeOfNSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La), ∀ P ∈ Hset Dw c a n, ∀ N N', admitted l N → admitted l N' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S),
      IsThValueAt J N x P y v ↔ IsThValueAt J N' x P y v

def BaseChangeSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La), ∀ P ∈ Hset Dw c a n,
    ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (z : FrPt Xo c T) (v : S), FrMap φ y z → IsThValue J x P y v → IsThValue J x P z (φ v)

def RationalSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La), ∀ P ∈ Hset Dw c a n,
    (∃! f, IsTh J a n x P f) ∧ ∀ f, IsTh J a n x P f → f ∈ sec Xo c a n

def BasisSpanSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (B : Set (Pol Dw c n)),
    (AddSubgroup.closure B : Set (Pol Dw c n)) = Hset Dw c a n →
    Submodule.span (𝓞 c.F) (thGenOn J B) = thAll J a n

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnSectionIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelPairAction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsRigCubIso {S' S : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.cm.F)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (m.cm.thetaPull t.PP.L t.cub.t)

def IsLevelAut (Xo : Moduli Dw l) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (r : Xo.X ≅ Xo.X)
    (ν : SABMap Xo.univ.t Xo.univ.t r.hom) : Prop :=
  r.hom ≫ Xo.s = Xo.s ∧
    (∀ a, (Xo.univ.eta (gM a)).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo.univ.etaA (gA a)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA a).left)

def CarriesSec {Xo : Moduli Dw l} {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull φ)) {x x' : Sp S ⟶ Xo.X}
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) : Prop :=
  ∃ pm : Gx x ⟶ Gx x',
    pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ ∧
    pm ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ∧
    ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx x).Opens)
      (hi : W ≤ (PPx x).U (fun _ => i))
      (hj : W ≤ pm ⁻¹ᵁ (PPx x').U (fun _ => j))
      (hw : W ≤ (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
        (LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U (fun _ => j, i)),
      (pm.appLE _ W hj).hom (s'.f (fun _ => j)) =
        ((snd (Over.mk x) Xo.univ.t.G).left.appLE _ W hw).hom (w.s (fun _ => j, i)).val *
          ((Gx x).presheaf.map (homOfLE hi).op).hom (s.f (fun _ => i))

variable {Xo : Moduli Dw l} {c : Coeff l}

def LevAct (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  ∃ (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
    IsLevelAut Xo gM gA r ν ∧ IsRigCubIso ν w ∧
      y'.x = y.x ≫ r.hom ∧ (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧ CarriesSec ν.cm.F w y.s y'.s

def CongM (l : Level H) (g g' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, g a - g' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)

def CongN (n : ℕ) (g g' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop := ∀ a, ∃ b, g a - g' a = n • b

def IsLevelPair (l : Level H) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∃ k : ℕ → (Dw.La →ₗ[𝓞 E] Dw.La),
    (∀ n m, 0 < n → 0 < m → CongN n (k (n * m)) (k n)) ∧
    (∀ n : ℕ, 0 < n → ∀ a b, Dw.EF (k n a) (k n b) ≡ Dw.EF a b [ZMOD (n : ℤ)]) ∧
    CongM l gM (k l.M) ∧ CongN l.A gA (k l.A)

def LevelAutExistsSt (Xo : Moduli Dw l) : Prop :=
  ∀ gM gA : Dw.La →ₗ[𝓞 E] Dw.La, IsLevelPair l gM gA →
    ∃ (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom), IsLevelAut Xo gM gA r ν

def IsLevelRep (l : Level H) {Γ : Type} [Group Γ] (ρM ρA : Γ → (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  (∀ g, IsLevelPair l (ρM g) (ρA g)) ∧
    CongM l (ρM 1) LinearMap.id ∧ CongN l.A (ρA 1) LinearMap.id ∧
    (∀ g h, CongM l (ρM (g * h)) (ρM g ∘ₗ ρM h)) ∧ (∀ g h, CongN l.A (ρA (g * h)) (ρA g ∘ₗ ρA h))

def LevActLawsSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (Γ : Type) [Group Γ] (ρM ρA : Γ → (Dw.La →ₗ[𝓞 E] Dw.La)), IsLevelRep l ρM ρA →
    ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
      (fun (g : Γ) y y' => LevAct (ρM g) (ρA g) y y')

theorem LevAct.congr {gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La} (hM : CongM l gM' gM) (hA : CongN l.A gA' gA)
    {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : LevAct gM gA y y') : LevAct gM' gA' y y' := by
  obtain ⟨r, ν, w, ⟨h0, h1, h2⟩, h3⟩ := h
  refine ⟨r, ν, w, ⟨h0, fun a => ?_, fun a => ?_⟩, h3⟩
  · have e : Xo.univ.eta (gM' a) = Xo.univ.eta (gM a) := by
      rw [show gM' a = (gM' a - gM a) + gM a by abel, Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
    rw [e]; exact h1 a
  · obtain ⟨b, hb⟩ := hA a
    have e : Xo.univ.etaA (gA' a) = Xo.univ.etaA (gA a) := by
      rw [show gA' a = (gA' a - gA a) + gA a by abel, Xo.univ.etaA_add, hb, Xo.univ.etaA_ker, _root_.one_mul]
    rw [e]; exact h2 a

end GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
end
end

