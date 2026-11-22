import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0185
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0186
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRoot
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FKum

variable {l : ℕ} [Fact l.Prime]

def tu (A : PAlg l) : A.A →* Γ(SU A, ⊤) :=
  ((toΓ A.Ug).toMonoidHom.comp (algebraMap A.U A.Ug).toMonoidHom).comp A.sharp

theorem tu_apply (A : PAlg l) (a : A.A) : tu A a = toΓ A.Ug (algebraMap A.U A.Ug (A.sharp a)) := rfl

theorem sharp_nat {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    PAlg.mapU f (A.sharp a) = B.sharp (PAlg.Hom.f f a) := by
  change PAlg.mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (PAlg.Hom.f f a))
  rw [PAlg.mapU_th]
  exact congrArg B.th (WittVector.map_teichmuller _ _ _)

theorem tu_nat {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    (Spec.map (CommRingCat.ofHom (PAlg.mapUg f))).appTop.hom (tu A a) = tu B (PAlg.Hom.f f a) := by
  rw [tu_apply, toΓ_nat, PAlg.mapUg_algebraMap, sharp_nat]; rfl

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem toΓ_hom (B : Type) [CommRing B] (x : Γ(Spec (CommRingCat.of B), ⊤)) :
    toΓ B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) = x :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id x

abbrev gU (B : PAlg l) : SU B ⟶ Spec (CommRingCat.of B.U) := Spec.map (CommRingCat.ofHom (algebraMap B.U B.Ug))

theorem tu_of_sharp {X : Scheme.{0}} (D : LineData X) (B : PAlg l) (a b : Spec (CommRingCat.of B.U) ⟶ D.Y)
    (h : a ≫ D.f = b ≫ D.f) (w : B.A)
    (hw : B.sharp w = (Scheme.ΓSpecIso (CommRingCat.of B.U)).hom.hom (D.u a b h).val)
    (h' : (gU B ≫ a) ≫ D.f = (gU B ≫ b) ≫ D.f) :
    tu B w = (D.u (gU B ≫ a) (gU B ≫ b) h').val := by
  rw [D.nat (gU B) a b h, tu_apply, hw, ← toΓ_nat, toΓ_hom]
  rfl

theorem exists_root (A : PAlg l) (n : ℕ) (w : (A.A)ˣ) : ∃ ω : (A.A)ˣ, ω ^ l ^ n = w := by
  have hs : ∀ (n : ℕ) (x : A.A), ∃ y : A.A, y ^ l ^ n = x := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := A.A) (p := l)).2 x
      obtain ⟨z, hz⟩ := ih y
      exact ⟨z, by rw [pow_succ, pow_mul, hz]; exact hy⟩
  obtain ⟨y, hy⟩ := hs n w
  have hu : IsUnit y := (isUnit_pow_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 (hy ▸ w.isUnit)
  obtain ⟨ω, rfl⟩ := hu
  exact ⟨ω, Units.ext (by simpa using hy)⟩

section Main
variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : Model l K} {C : Type 1} [Category.{0} C]

abbrev Ao (G : C ⥤ El M.P) (c : C) : PAlg l := (G.obj c).1.obj

abbrev mp (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : Ao G c ⟶ Ao G c' := (G.map φ).1.hom

abbrev sg (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : SU (Ao G c') ⟶ SU (Ao G c) :=
  Spec.map (CommRingCat.ofHom (PAlg.mapUg (mp G φ)))

abbrev sgU (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') :
    Spec (CommRingCat.of (Ao G c').U) ⟶ Spec (CommRingCat.of (Ao G c).U) :=
  Spec.map (CommRingCat.ofHom (PAlg.mapU (mp G φ)))

theorem sg_gU (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : sg G φ ≫ gU (Ao G c) = gU (Ao G c') ≫ sgU G φ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun x => PAlg.mapUg_algebraMap _ x

theorem sg_comp (G : C ⥤ El M.P) {c c' c'' : C} (φ : c ⟶ c') (ψ : c' ⟶ c'') :
    sg G (φ ≫ ψ) = sg G ψ ≫ sg G φ := by
  have e : mp G (φ ≫ ψ) = mp G φ ≫ mp G ψ := congrArg (fun t => t.1.hom) (G.map_comp φ ψ)
  rw [sg, e]
  exact (congrArg Spec.map ((UgR l).map_comp _ _)).trans (Spec.map_comp _ _)

theorem sgU_pt (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : sgU G φ ≫ (G.obj c).2.1 = (G.obj c').2.1 :=
  congrArg Subtype.val (G.map φ).2

variable {D : LineData M.X} {D' : LineData (gb M)} {π : D'.Y ⟶ D.Y} {G : C ⥤ El M.P}

theorem hr_eq (hBC : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (Λ : Lift G D)
    (p' : ∀ c, SU (Ao G c) ⟶ D'.Y) (hπ : ∀ c, p' c ≫ π = gU (Ao G c) ≫ Λ.p c) {c c' : C} (φ : c ⟶ c')
    (h : (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f) :
    tu (Ao G c') (Λ.w φ).val = (D'.u (sg G φ ≫ p' c) (p' c') h).val := by
  have h0 : (sgU G φ ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp, sgU_pt]
  have h1 : (gU (Ao G c') ≫ sgU G φ ≫ Λ.p c) ≫ D.f = (gU (Ao G c') ≫ Λ.p c') ≫ D.f := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (sgU G φ), h0, Category.assoc]
  have h2 : ((sg G φ ≫ p' c) ≫ π) ≫ D.f = (p' c' ≫ π) ≫ D.f := by
    have key : ∀ {V : Scheme.{0}} (t : V ⟶ D'.Y), (t ≫ π) ≫ D.f =
        (t ≫ D'.f) ≫ (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) := fun t => by
      rw [Category.assoc, hBC.1, Category.assoc]
    rw [key, key, h]
  rw [tu_of_sharp D _ _ _ h0 _ (Λ.hw φ h0) h1, hBC.2.2 _ _ _ h h2]
  refine congrArg Units.val (u_congr D ?_ (hπ c').symm _ _)
  rw [Category.assoc, hπ, ← Category.assoc, ← sg_gU, Category.assoc]

abbrev tuU (A : PAlg l) : (A.A)ˣ →* (Γ(SU A, ⊤))ˣ := Units.map (tu A)

abbrev chU {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) : ((Ao G c₂).A)ˣ :=
  Units.map (PAlg.Hom.f (mp G ψ)).toMonoidHom a * b * c⁻¹

theorem map_tuU {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) :
    Units.map (sg G ψ).appTop.hom.toMonoidHom (tuU (Ao G c₁) a) =
      tuU (Ao G c₂) (Units.map (PAlg.Hom.f (mp G ψ)).toMonoidHom a) :=
  Units.ext (tu_nat (mp G ψ) a.val)

theorem chain_val {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) :
    Units.map (sg G ψ).appTop.hom.toMonoidHom (tuU (Ao G c₁) a) * tuU (Ao G c₂) b * (tuU (Ao G c₂) c)⁻¹ =
      tuU (Ao G c₂) (chU G ψ a b c) := by
  rw [map_tuU, chU, map_mul, map_mul, map_inv]

theorem chain_pow {c₀ c₁ c₂ : C} (p' : ∀ c, SU (Ao G c) ⟶ D'.Y) (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂)
    (hχ : φ ≫ ψ = χ) (q : ℕ) (a : (Γ(SU (Ao G c₁), ⊤))ˣ) (b c : (Γ(SU (Ao G c₂), ⊤))ˣ)
    (h₁ : (sg G φ ≫ p' c₀) ≫ D'.f = p' c₁ ≫ D'.f) (h₂ : (sg G ψ ≫ p' c₁) ≫ D'.f = p' c₂ ≫ D'.f)
    (h₃ : (sg G χ ≫ p' c₀) ≫ D'.f = p' c₂ ≫ D'.f)
    (ha : a ^ q = D'.u (sg G φ ≫ p' c₀) (p' c₁) h₁) (hb : b ^ q = D'.u (sg G ψ ≫ p' c₁) (p' c₂) h₂)
    (hc : c ^ q = D'.u (sg G χ ≫ p' c₀) (p' c₂) h₃) :
    (Units.map (sg G ψ).appTop.hom.toMonoidHom a * b * c⁻¹) ^ q = 1 := by
  have h₄ : (sg G ψ ≫ sg G φ ≫ p' c₀) ≫ D'.f = (sg G ψ ≫ p' c₁) ≫ D'.f := by
    rw [Category.assoc, h₁, Category.assoc]
  rw [mul_pow, mul_pow, inv_pow, ← map_pow, ha, hb, hc, ← D'.nat (sg G ψ) _ _ h₁, D'.coc _ _ _ h₄ h₂]
  rw [u_congr D' (a' := sg G χ ≫ p' c₀) (b' := p' c₂) _ rfl _ h₃, mul_inv_cancel]
  rw [← hχ, sg_comp, Category.assoc]

abbrev tuP (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) (c : C) :
    ((Ao G c).A)ˣ →* (Γ((probe H r (G ⋙ CategoryOfElements.π _) n).U c, ⊤))ˣ := tuU (Ao G c)

theorem chain_valP (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) {c₁ c₂ : C} (ψ : c₁ ⟶ c₂)
    (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) :
    Units.map ((probe H r (G ⋙ CategoryOfElements.π _) n).S.map ψ).unop.appTop.hom.toMonoidHom (tuP H r G n c₁ a) *
      tuP H r G n c₂ b * (tuP H r G n c₂ c)⁻¹ = tuP H r G n c₂ (chU G ψ a b c) :=
  chain_val G ψ a b c

theorem pow_field (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) (c : C)
    (f : LocallyConstant (SU (Ao G c)) (ZMod (l ^ n))) (u : ((Ao G c).A)ˣ)
    (h : IsPow (r.zeta (Ao G c) n) f (tu (Ao G c) u.val)) :
    IsPow ((probe H r (G ⋙ CategoryOfElements.π _) n).ζ c) f (tuP H r G n c u).val := h

theorem kum_of (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2) (p' : ∀ c, SU (Ao G c) ⟶ D'.Y)
    (hf : ∀ c, p' c ≫ D'.f = geomPt M (Ao G c) (G.obj c).2) (ω : ∀ (c c' : C), (c ⟶ c') → ((Ao G c').A)ˣ)
    (hfh : ∀ {c c' : C} (φ : c ⟶ c'), (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f)
    (hr : ∀ {c c' : C} (φ : c ⟶ c'), tuU (Ao G c') (ω c c' φ) ^ l ^ n = D'.u (sg G φ ≫ p' c) (p' c') (hfh φ))
    (hz : ∀ s : ComposableArrows C 2, IsPow ((probe H r (G ⋙ CategoryOfElements.π _) n).ζ (s.obj (Fin.last 2))) (z s)
      (tuP H r G n (s.obj (Fin.last 2)) (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2)))).val) :
    Nonempty (IsKumCoc (pts H r M G n) D' z) :=
  ⟨{ p := p'
     hp := hf
     r := fun {c c'} φ => tuP H r G n c' (ω c c' φ)
     hr := fun φ => hr φ
     hz := fun s => by
       rw [chain_valP]
       exact hz s }⟩

theorem log_of (hN : LcNat) (H : RIn l) (r : Roots l) {D : LineData M.X} (G : C ⥤ El M.P) (n : ℕ) (Λ : Lift G D)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2)
    (h : ∀ s : ComposableArrows C 2, IsLog (Ao G (s.obj (Fin.last 2))) n (tei (Ao G (s.obj (Fin.last 2))) (Λ.r s))
      ((ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA (Ao G (s.obj (Fin.last 2))) n (z s))) :
    Λ.IsCoc n (tCo G n 2 (lcCo hN H r G n 2 z)) := h

theorem r_eq {D : LineData M.X} (Λ : Lift G D) (n : ℕ) (ω : ∀ (c c' : C), (c ⟶ c') → ((Ao G c').A)ˣ)
    (hω : ∀ (c c' : C) (φ : c ⟶ c'), ω c c' φ ^ l ^ n = Λ.w φ) (s : ComposableArrows C 2) :
    Λ.r s = (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2))) ^ l ^ n := by
  rw [chU, mul_pow, mul_pow, inv_pow, ← map_pow, hω, hω, hω]
  rfl

end Main

theorem fKum (hR : RootPow) (hL : LcLog) : FKum := by
  intro hN l _ H r K M D D' π hBC C _ G Λ n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hb : ∀ c, ∃ b : SU (Ao G c) ⟶ D'.Y, b ≫ π = gU (Ao G c) ≫ Λ.p c ∧
      b ≫ D'.f = geomPt M (Ao G c) (G.obj c).2 := fun c =>
    hBC.2.1 _ _ _ (by rw [Category.assoc, Λ.hp, geomPt_fst])
  choose p' hπ hf using hb
  have hω : ∀ (c c' : C) (φ : c ⟶ c'), ∃ ω : ((Ao G c').A)ˣ, ω ^ l ^ n = Λ.w φ := fun c c' φ => exists_root _ n _
  choose ω hω using hω
  have hfh : ∀ {c c' : C} (φ : c ⟶ c'), (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f := by
    intro c c' φ
    rw [Category.assoc, hf, hf]
    exact (pts H r M G n).nat φ
  have hr : ∀ {c c' : C} (φ : c ⟶ c'), tuU (Ao G c') (ω c c' φ) ^ l ^ n = D'.u (sg G φ ≫ p' c) (p' c') (hfh φ) := by
    intro c c' φ
    rw [← map_pow, hω c c' φ]
    exact Units.ext (hr_eq hBC Λ p' hπ φ _)
  have hz : ∀ s : ComposableArrows C 2, ∃ f : LocallyConstant (SU (Ao G (s.obj (Fin.last 2)))) (ZMod (l ^ n)),
      IsPow (r.zeta (Ao G (s.obj (Fin.last 2))) n) f
        (tu (Ao G (s.obj (Fin.last 2))) (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2))).val) := by
    intro s
    refine (hR (l ^ n) _ _).1 _ ?_
    have h := chain_pow p' (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (by rw [← s.map_comp]; rfl) (l ^ n)
      (tuU _ (ω _ _ (s.map' 0 1))) (tuU _ (ω _ _ (s.map' 1 2))) (tuU _ (ω _ _ (s.map' 0 2)))
      (hfh _) (hfh _) (hfh _) (hr _) (hr _) (hr _)
    rw [chain_val] at h
    exact congrArg Units.val h
  choose z hz using hz
  refine ⟨z, kum_of H r G n z p' hf ω hfh hr fun s => pow_field H r G n _ _ _ (hz s), log_of hN H r G n Λ z fun s => ?_⟩
  have h := hL l H r (Ao G (s.obj (Fin.last 2))) (G.obj (s.obj (Fin.last 2))).1.property n _ (z s) (hz s)
  rw [← Units.val_pow_eq_pow_val, ← r_eq Λ n ω hω s] at h
  exact h

end GlobalTheory.CompanionTheory.FKum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorialAcr
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogMulPf

def ratHom {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) : ℚ →+* S :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom S) (fun y => by
    have hy : (y : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    have h := hu _ (Int.natAbs_ne_zero.2 hy)
    rcases Int.natAbs_eq (y : ℤ) with e | e
    · rw [e]; simpa using h
    · rw [e]; simpa using h)

theorem inv_smul_eq {S : Type} [CommRing S] [Algebra ℚ S] (m : ℕ) (hm : m ≠ 0) (x : S) :
    ((m : ℚ)⁻¹) • x = Ring.inverse (m : S) * x := by
  have h1 : (m : S) * algebraMap ℚ S (m : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ S), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]
  have h : IsUnit (m : S) := IsUnit.of_mul_eq_one _ h1
  apply h.mul_left_cancel
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, h1, Ring.mul_inverse_cancel _ h]

theorem core (hLA : LogAlg) {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) (T : Subring S) (x y : S)
    (hx : ∀ k : ℕ, Ring.inverse (k.factorial : S) * x ^ k ∈ T)
    (hy : ∀ k : ℕ, Ring.inverse (k.factorial : S) * y ^ k ∈ T) :
    (∀ k : ℕ, Ring.inverse (k.factorial : S) * (x + y + x * y) ^ k ∈ T) ∧ ∀ N : ℕ, ∃ c ∈ T,
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) *
          (Ring.inverse ((k + 1).factorial : S) * (x + y + x * y) ^ (k + 1)) =
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * x ^ (k + 1)) +
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * y ^ (k + 1)) +
          (N.factorial : S) * c := by
  letI : Algebra ℚ S := (ratHom hu).toAlgebra
  have e : ∀ (k : ℕ) (z : S), ((k.factorial : ℚ)⁻¹) • z ^ k = Ring.inverse (k.factorial : S) * z ^ k :=
    fun k z => inv_smul_eq _ k.factorial_ne_zero _
  have := hLA S T (fun k z => ((k.factorial : ℚ)⁻¹) • z ^ k) (fun _ _ => rfl) x y
    (fun k => by simp only [e]; exact hx k) (fun k => by simp only [e]; exact hy k)
  simpa only [e] using this

theorem sum_eq_of_coe {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (T : Subalgebra R S) (f f' f'' : ℕ → T)
    (N : ℕ) (c : T)
    (e : ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f'' (k + 1) : S) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f (k + 1) : S) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f' (k + 1) : S) + (N.factorial : S) * (c : S)) :
    ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f'' (k + 1) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f (k + 1) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f' (k + 1) + (N.factorial : T) * c := by
  apply Subtype.ext
  push_cast
  exact e

variable {l : ℕ} [Fact l.Prime]

theorem factorial_acr (A : PAlg l) (n : ℕ) : (((l * n).factorial : ℕ) : A.Acr n) = 0 := by
  obtain ⟨d, hd⟩ := ACris.pow_dvd_factorial (p := l) (le_refl (l * n))
  rw [hd, Nat.cast_mul, Nat.cast_pow, A.pow_l_acr, zero_mul]

theorem isLog_mul (hLA : LogAlg) (A : PAlg l) (n : ℕ) (w w' : A.W) (y y' : A.Acr n)
    (hy : IsLog A n w y) (hy' : IsLog A n w' y') : IsLog A n (w * w') (y + y') := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have hab : algebraMap A.W (WL l A.A) (w * w' - 1) =
      algebraMap A.W (WL l A.A) (w - 1) + algebraMap A.W (WL l A.A) (w' - 1) +
        algebraMap A.W (WL l A.A) (w - 1) * algebraMap A.W (WL l A.A) (w' - 1) := by
    simp only [map_sub, map_mul, map_one]; ring
  obtain ⟨hT, hN⟩ := core hLA (fun m hm => A.isUnit_natCast hm) A.Acr0.toSubring
    (algebraMap A.W (WL l A.A) (w - 1)) (algebraMap A.W (WL l A.A) (w' - 1))
    (fun k => by have h := (g k).2; rw [hg k] at h; exact h)
    (fun k => by have h := (g' k).2; rw [hg' k] at h; exact h)
  have hmem : ∀ k, dpw k (w * w' - 1) ∈ A.Acr0 := fun k => by
    rw [dpw, hab]; exact hT k
  obtain ⟨c, hc, e⟩ := hN (l * n)
  refine ⟨fun k => ⟨dpw k (w * w' - 1), hmem k⟩, fun _ => rfl, ?_⟩
  have e0 := sum_eq_of_coe A.Acr0 g g' (fun k => ⟨dpw k (w * w' - 1), hmem k⟩) (l * n) ⟨c, hc⟩ (by
    simp only [hg, hg']
    simp only [dpw, hab]
    exact e)
  have e1 := congrArg (A.mkAcr n) e0
  simp only [map_add, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at e1
  rw [e1, factorial_acr, zero_mul, add_zero]

theorem logMul : CrystallineSemistableComparison.E.LogAlg → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul :=
  fun h _ _ _ A n w w' y y' _ _ hy hy' => isLog_mul h A n w w' y y' hy hy'

end GlobalTheory.CompanionTheory.LogMulPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQShiftLe
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.ChartSections

theorem finrank_chartLatQ_shift_le : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (b : K → ℤ) (e : K → ℕ) (M : ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, e k ≤ M) →
    FiniteDimensional ℚ (chartLatQ y (b + fun _ => (M : ℤ)) 1) →
    Module.finrank ℚ (chartLatQ y (b + fun k => (e k : ℤ)) 1) ≤
      Module.finrank ℚ (chartLatQ y (b + fun _ => (M : ℤ)) 1) := by
  intro K _ ι _ Ω _ _ y b e M hy he hfd
  choose j hj using hy
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ (M - e k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ chartLatQ y (b + fun k => (e k : ℤ)) 1,
      s * ∏ k, y ⟨k, j k⟩ ^ (M - e k) ∈ chartLatQ y (b + fun _ => (M : ℤ)) 1 := by
    intro s hs c hc
    have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun k => (e k : ℤ) : K → ℤ) k)) ∈ chartRingQ y c := hs c hc
    have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingQ y c :=
      fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ (M - e k) ∈ chartRingQ y c :=
      prod_mem fun k _ => pow_mem (hq k) _
    have heq : s * (∏ k, y ⟨k, j k⟩ ^ (M - e k)) *
          ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun _ => (M : ℤ) : K → ℤ) k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun k => (e k : ℤ) : K → ℤ) k))) *
          ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ (M - e k) := by
      rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck := hc k
      have hek := he k
      have hz : y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun _ => (M : ℤ) : K → ℤ) k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun k => (e k : ℤ) : K → ℤ) k)) * (y ⟨k, c k⟩ ^ (M - e k))⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
        congr 1
        simp only [Pi.add_apply, Nat.cast_one, one_mul]
        omega
      rw [hz, div_pow, div_eq_mul_inv]
      ring
    show s * (∏ k, y ⟨k, j k⟩ ^ (M - e k)) *
      ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun _ => (M : ℤ) : K → ℤ) k)) ∈ chartRingQ y c
    rw [heq]
    exact mul_mem h1 h2
  let f : chartLatQ y (b + fun k => (e k : ℤ)) 1 →ₗ[ℚ] chartLatQ y (b + fun _ => (M : ℤ)) 1 :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ (M - e k), hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end GlobalTheory.CompanionTheory.ChartSections
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_to_cech_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j) := by
  first | exact @GlobalTheory.CompanionTheory.OmCech.formToCO_bijective | exact GlobalTheory.CompanionTheory.OmCech.formToCO_bijective | (intros; apply GlobalTheory.CompanionTheory.OmCech.formToCO_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmulStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_to_cech_smul : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (a j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j),
    formToCO q U a j (r • x) = r • formToCO q U a j x := by
  first | exact @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul | exact GlobalTheory.CompanionTheory.OmBridge.formToCO_smul | (intros; apply GlobalTheory.CompanionTheory.OmBridge.formToCO_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobIdem
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FrobLc

variable {l : ℕ} [Fact l.Prime]

theorem frob_idem (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) : A.frob e = e := by
  change e ^ l = e
  have h := IsIdempotentElem.pow_succ_eq (l - 1) he
  rwa [Nat.sub_add_cancel (Fact.out : l.Prime).one_lt.le] at h

theorem lcRes_id (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) :
    lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (RingHom.id A.Ug))) f = f := by
  have e : Spec.map (CommRingCat.ofHom (RingHom.id A.Ug)) = 𝟙 (SU A) := by
    change Spec.map (𝟙 (CommRingCat.of A.Ug)) = 𝟙 _
    exact Spec.map_id _
  rw [e]
  ext x
  rfl

theorem phi_lcA (hN : LcNat) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU A) (ZMod (l ^ n))) : A.phi n (lcA A n f) = lcA A n f := by
  have h := (hN l H A hA n).1 A hA A.frob A.pdOk_frob (RingHom.id A.Ug)
    (fun e he => by rw [frob_idem A e he]; rfl) f
  rw [lcRes_id] at h
  exact h

section Gen
universe w w' u v u' v'
variable {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
  {σ : R →+* R'} {ρ : R' →+* R'}

theorem cls_congr {K : CrystallineSemistableComparison.Cx.{w} R} {k : ℕ} {x y : K.X k} (h : x = y) (hx : K.d k x = 0) (hy : K.d k y = 0) :
    K.cls x hx = K.cls y hy := by
  subst h; rfl

theorem pull_fix (m : Mor F F' σ) (p : Mor F' F' ρ) (j : ℕ) (h : ∀ z, p.pullC j (m.pullC j z) = m.pullC j z)
    (c : CH.H F j) : p.pull j (m.pull j c) = m.pull j c := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact cls_congr (h z) _ _
end Gen

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem phi_lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ)
    (z : Cn (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L j) :
    (phiMor M.P n).pullC j ((lcM hN H r M n).pullC j z) = (lcM hN H r M n).pullC j z := by
  funext s
  exact phi_lcA hN H _ (s.obj (Fin.last j)).1.property n _

theorem fPhi : CrystallineSemistableComparison.E.FPhi := fun hN l _ H r K M n j x =>
  pull_fix (lcM hN H r M n) (phiMor M.P n) j (phi_lcM hN H r M n j) ((pts H r M (𝟭 _) n).et 0 j x)

end GlobalTheory.CompanionTheory.FrobLc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforwardStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_resolution_lift_pushforward : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G'), ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  first | exact @GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift | exact GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift | (intros; apply GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecompositionStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_exp_product_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤) → 𝔨 ≤ 𝔤 → 𝔟 ≤ 𝔤 → 𝔤 ≤ 𝔨 ⊔ 𝔟 → ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | exact GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | (intros; apply GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnitStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_star_closed_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | exact GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | (intros; apply GlobalTheory.CompanionTheory.LieStable.lieAlg_stable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheaf_pull_connecting_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S'.map (push f)) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n),
    hPull f α.τ₁ (n + 1) (H.δ hS n (n + 1) rfl x) = H.δ hS' n (n + 1) rfl (hPull f α.τ₃ n x) := by
  first | exact @GlobalTheory.CompanionTheory.CechDelta.hPull_δ | exact GlobalTheory.CompanionTheory.CechDelta.hPull_δ | (intros; apply GlobalTheory.CompanionTheory.CechDelta.hPull_δ <;> assumption)
end

