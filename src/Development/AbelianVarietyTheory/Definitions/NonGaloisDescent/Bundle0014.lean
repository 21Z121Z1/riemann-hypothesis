import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal

namespace GlobalTheory.BSP

section Cover

variable {l : ℕ} {R : Type} [CommRing R]

abbrev adI (B : Obj l R) : Ideal B.A := Ideal.span {(l : B.A)} ⊔ B.I

theorem adI_pow_le {B B' : Obj l R} (f : Hom B B') (m : ℕ) : adI B ^ m ≤ (adI B' ^ m).comap f.f := by
  refine le_trans (Ideal.pow_right_mono ?_ m) (Ideal.le_comap_pow f.f m)
  refine sup_le ?_ fun a ha => Ideal.mem_sup_right (f.f_I a ha)
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

def qmap {B B' : Obj l R} (f : Hom B B') (m : ℕ) : (B.A ⧸ adI B ^ m) →+* (B'.A ⧸ adI B' ^ m) :=
  Ideal.quotientMap _ f.f (adI_pow_le f m)

theorem qmap_mk {B B' : Obj l R} (f : Hom B B') (m : ℕ) (a : B.A) :
    qmap f m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f.f a) := rfl

structure IsPO {B C B' C' : Obj l R} (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C') : Prop where
  comm : k'.comp h = h'.comp k
  po : ∀ m : ℕ, CategoryTheory.IsPushout (CommRingCat.ofHom (qmap h m)) (CommRingCat.ofHom (qmap k m))
    (CommRingCat.ofHom (qmap k' m)) (CommRingCat.ofHom (qmap h' m))

structure Stable {B C : Obj l R} (h : Hom B C) : Prop where
  flat : ∀ m : ℕ, (qmap h m).Flat
  po : ∀ (B' : Obj l R) (k : Hom B B'), ∃ (C' : Obj l R) (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h'

structure Cover {B C : Obj l R} (h : Hom B C) : Prop where
  stable : Stable h
  ff : ∀ m : ℕ, (qmap h m).FaithfullyFlat

structure IsLoc {B C : Obj l R} (s : B.A) (h : Hom B C) : Prop where
  away : ∀ m : ℕ, letI := (qmap h m).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (adI B ^ m) s) (C.A ⧸ adI C ^ m)
  univ : ∀ (Q : Obj l R) (a : Hom B Q), IsUnit (a.f s) → ∃ c : Hom C Q, c.comp h = a

end Cover

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

structure Eval (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] where
  fin : Module.Finite B.A N
  proj : Module.Projective B.A N

  v : ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q), Hom bk.prism Q → N →ₛₗ[a.f] (Fin d → Q.A)
  bc : ∀ {Q} (a : Hom B Q) (g : Hom bk.prism Q), SemiBC (v a g)
  v_ε : ∀ {Q} (a : Hom B Q) (g g' : Hom bk.prism Q) (x : N), v a g x = (S.ε g g').mulVec (v a g' x)
  v_nat : ∀ {Q Q'} (c : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) (i : Fin d),
    v (c.comp a) (c.comp g) x i = c.f (v a g x i)

def IsPsi {S : Strat bk d} {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (Ψ : N →ₛₗ[B.D.φ] N) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
    BK.hf g bk.E ^ S.a • V.v a g (Ψ x) =
      a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)

def IsCoord {S : Strat bk d} {M : FCrys l ↥(OL K)} (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism))
    {B : Obj l ↥(OL K)} (V : Eval S B (M.M B)) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B),
    M.tr a x = ∑ i, V.v a g x i • M.tr g (e i)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped NNReal

namespace GlobalTheory.BSP.Height

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

def bas : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * ht.Z

def Rel {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀)) : Prop :=
  ∀ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (BK.hf f) Ff → IsDiscMap (BK.hf g) Fg →
    toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff * ε) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg

theorem rel_one {B : Obj l ↥(OL K)} (u : B.A) (f : Hom bk.prism B) : ht.Rel u f f 1 := fun Ff Fg hf hg => by
  rw [hf.unique hg, mul_one]

end GlobalTheory.BSP.Height
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def TeichTriv (χ : Formalism.L2.Host.HChar H.E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 H.E), OverP H H.pde w ∨ OverP H H.pde' w →
    ∀ x : (w.adicCompletion H.E)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1

variable {H} {χ χ' : Formalism.L2.Host.HChar H.E}

theorem isUnitAt_of_pow_eq_one {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {x : (w.adicCompletion E)ˣ}
    (hx : x ^ (Ideal.absNorm w.asIdeal - 1) = 1) : IsUnitAt w x := by
  have h1 : Ideal.absNorm w.asIdeal - 1 ≠ 0 := by have := GlobalTheory.Mem.WildChar.one_lt_absNorm w; omega
  have := congrArg (fun y : (w.adicCompletion E)ˣ => Valued.v (y : w.adicCompletion E)) hx
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
  exact (pow_eq_one_iff_left h1).1 this

theorem unrAt_of_tameAt_of_teich {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (ht : χ.TameAt w) (h : ∀ x : (w.adicCompletion E)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1) : χ.UnrAt w := by
  intro x hx
  have hx' : Valued.v (x : w.adicCompletion E) = 1 := hx
  obtain ⟨ζ, h1, h2⟩ := GlobalTheory.Mem.WildChar.exists_rootOfUnity_congr w hx'
  have hζ : Valued.v ζ = 1 := by
    rw [← hx']
    apply Valuation.map_eq_of_sub_lt
    rwa [hx']
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  let z : (w.adicCompletion E)ˣ := Units.mk0 ζ h0
  have hz : χ.loc w z = 1 := h z (Units.ext (by simpa [z] using h1))
  have hu : IsUnitAt w (x * z⁻¹) := by simp [IsUnitAt, z, hx', hζ]
  have hu1 : Valued.v (((x * z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) < 1 := by
    have e : ((x * z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 = (x - ζ) * ζ⁻¹ := by
      simp [z, sub_mul, h0]
    rw [e, map_mul, map_inv₀, hζ, inv_one, mul_one, Valuation.map_sub_swap]
    exact h2
  have h3 := ht _ hu (by simpa using GlobalTheory.Mem.WildChar.le_exp_neg_one_of_lt_one hu1)
  rwa [map_mul, map_inv, hz, inv_one, mul_one] at h3

namespace TeichTriv

theorem one : TeichTriv H 1 := fun _ _ _ _ => rfl

theorem mul (h : TeichTriv H χ) (h' : TeichTriv H χ') : TeichTriv H (χ * χ') := fun w hw x hx => by
  rw [HChar.loc_mul, h w hw x hx, h' w hw x hx, one_mul]

theorem inv (h : TeichTriv H χ) : TeichTriv H χ⁻¹ := fun w hw x hx => by rw [HChar.loc_inv, h w hw x hx, inv_one]

theorem of_unr (h : ∀ w, OverP H H.pde w ∨ OverP H H.pde' w → χ.UnrAt w) : TeichTriv H χ :=
  fun w hw x hx => h w hw x (isUnitAt_of_pow_eq_one hx)

theorem pow_eq_one (h : TeichTriv H χ) {w : HeightOneSpectrum (𝓞 H.E)} (hw : OverP H H.pde w ∨ OverP H H.pde' w)
    {x : (w.adicCompletion H.E)ˣ} (hx : IsUnitAt w x) : ∃ n : ℕ, χ.loc w x ^ (Ideal.absNorm w.asIdeal ^ n) = 1 :=
  (GlobalTheory.Mem.WildChar.orders_on_units _ χ w).2 (h w hw) x hx

theorem unrAt (h : TeichTriv H χ) {w : HeightOneSpectrum (𝓞 H.E)} (hw : OverP H H.pde w ∨ OverP H H.pde' w) (ht : χ.TameAt w) :
    χ.UnrAt w := unrAt_of_tameAt_of_teich ht (h w hw)

end TeichTriv

theorem not_teichTriv_of_isDelta {p : ℕ} (hd : IsDelta (H := H) p χ) {w : HeightOneSpectrum (𝓞 H.E)} (hp : OverP H p w)
    (hw : OverP H H.pde w ∨ OverP H H.pde' w) : ¬ TeichTriv H χ := fun h => by
  have := (hd.ine w hp 1).1 fun x hx => by rw [pow_one, h.unrAt hw (hd.tame w) x hx]
  omega

end Host

namespace LamDat

variable {D : D7} (Z : LamDat D)

def Teich : Prop := ∀ a, TeichTriv D.host (Z.chi a)

variable {Z}

theorem Teich.lambda_local_teichmuller (h : Z.Teich) (l : ℕ) (j a : Fin D.R.m) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w) {x : (w.adicCompletion D.host.E)ˣ}
    (hx : x ^ (Ideal.absNorm w.asIdeal - 1) = 1) :
    (Z.lam0 l j a).loc w x = (Z.C.mu0 j).loc w x * (Z.C.delAt l).loc w x := by
  unfold lam0
  rw [HChar.loc_mul, HChar.loc_mul, HChar.loc_inv, h a w hw x hx, inv_one, mul_one]

theorem Teich.not_mul_del (h : Z.Teich) (a : Fin D.R.m) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : OverP D.host D.host.pde w) :
    ¬ TeichTriv D.host (Z.chi a * Z.C.del) := fun h' => by
  have h1 := (h a).inv.mul h'
  rw [inv_mul_cancel_left] at h1
  exact not_teichTriv_of_isDelta Z.C.isDel hw (Or.inl hw) h1

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsLamTieFull (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      (∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)) ∧
      ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
        ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ IsLam X Z i (atSide X b ι) lam j a s ∧
          IsThOf X i (atSide X b ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

variable {X} {Z : LamDat D}

theorem IsLam.range {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {j a : Fin D.R.m} {s : ℕ} (h : IsLam X Z i ι lam j a s) :
    1 ≤ s ∧ s ≤ BlochKatoReduction.Gen.NFun D.R + 1 :=
  ⟨by exact_mod_cast h.2.1.2.1, by exact_mod_cast h.2.1.2.2⟩

theorem isLamTieFull_of_labels (J A : ∀ i, X.abelian₂ i → Fin D.R.m) (S : ∀ i, X.abelian₂ i → ℕ)
    (hS : ∀ i, X.NonzeroIndexPlace i → ∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i)
    (hι : ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, IsLam X Z i (atSide X (X.sideL i lam) ι) lam (J i lam) (A i lam) (S i lam) ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) (S i lam) (Z.kap (J i lam) (A i lam) (S i lam)) (cond0 D.host Z.w0)
          (Z.lam0 (X.l i) (J i lam) (A i lam)))
    (hall : ∀ i, X.NonzeroIndexPlace i → ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
      ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ J i lam = j ∧ A i lam = a ∧ S i lam = s) : IsLamTieFull X Z := fun i hi => by
  obtain ⟨ι, h1, h2⟩ := hι i hi
  refine ⟨hS i hi, ι, h1, fun lam => ⟨_, _, _, h2 lam⟩, fun j a s b hs hs' => ?_⟩
  obtain ⟨lam, rfl, rfl, rfl, rfl⟩ := hall i hi j a s b hs hs'
  exact ⟨lam, rfl, h2 lam⟩

namespace IsLamTieFull

theorem isLamTie (h : IsLamTieFull X Z) : IsLamTie X Z := fun i hi =>
  let ⟨h0, ι, h1, h2, _⟩ := h i hi
  ⟨h0, ι, h1, h2⟩

theorem exists_labels (h : IsLamTieFull X Z) {i : X.Tw} (hi : X.NonzeroIndexPlace i) (j : Fin D.R.m) {s : ℕ} (b : Bool) (hs : 1 ≤ s)
    (hs' : s ≤ BlochKatoReduction.Gen.NFun D.R + 1) : ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ X.jL i lam = j.1 + 1 ∧ X.s2 i lam = 2 * (s : ℤ) :=
  let ⟨_, _, _, _, h3⟩ := h i hi
  let ⟨lam, e, hl, _⟩ := h3 j j s b hs hs'
  ⟨lam, e, hl.1.symm, hl.2.1.1⟩

theorem nonempty (h : IsLamTieFull X Z) {i : X.Tw} (hi : X.NonzeroIndexPlace i) : Nonempty (X.abelian₂ i) :=
  let ⟨lam, _⟩ := h.exists_labels hi ⟨0, by have := D.R.two_le_m; omega⟩ true le_rfl (by omega)
  ⟨lam⟩

end IsLamTieFull

example {i : X.Tw} (hi : X.NonzeroIndexPlace i) (h : IsEmpty (X.abelian₂ i)) : ¬ IsLamTieFull X Z := fun h' => (h'.nonempty hi).elim h.false

example (h : IsLamTieFull X Z) {i : X.Tw} (hi : X.NonzeroIndexPlace i) : Nontrivial (X.abelian₂ i) := by
  obtain ⟨x, hx, -⟩ := h.exists_labels hi ⟨0, by have := D.R.two_le_m; omega⟩ true le_rfl (by omega)
  obtain ⟨y, hy, -⟩ := h.exists_labels hi ⟨0, by have := D.R.two_le_m; omega⟩ false le_rfl (by omega)
  exact ⟨x, y, fun e => by rw [e, hy] at hx; cases hx⟩

example (Z : LamDat D) : TeichTriv D.host Z.C.eta := TeichTriv.of_unr fun w _ => Z.C.isEta.unr w

example (h : Z.Teich) (a : Fin D.R.m) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : OverP D.host D.host.pde w)
    (ho : Odd (Ideal.absNorm w.asIdeal)) : (Z.chi a).loc w (-1) = 1 :=
  h a w (Or.inl hw) _ (Even.neg_one_pow (Nat.Odd.sub_odd ho odd_one))

end Record

end GlobalTheory.LamTie
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw

variable (D : D7)

def SupG : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b g, ∀ f ∈ D.nexp.Bsup i j b,
  D.nexp.actG i j b g f ∈ D.nexp.Bsup i j b

def SupFull : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (D.nexp.Bsup i j b).FG ∧
  Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) = ⊤

def SupHk : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ f ∈ D.nexp.Bsup i j b,
  D.nexp.hkF i j b k P f ∈ D.nexp.Bsup i j b

def UnivSup (E : XD D) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M,
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (D.ntw.S0 i) → Disjoint Q (D.nexp.lev i j b a) →
  ∃ Xi : DelQM D.host (D.ntw.l i) Q M →₀ D.nexp.Fm i j b,
    D.nexp.thU i j b Q M a = Xi.sum (fun δ f => f ⊗ₜ[D.ntw.O i] AddMonoidAlgebra.single δ (1 : D.ntw.O i)) ∧
    ∀ δ, Xi δ ∈ Fm0 D.nexp i j b ∧ ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ D.nexp.Bsup i j b

def HkComm : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P k' P', HkIdx i k P → HkIdx i k' P' →
  Commute (D.nexp.hkF i j b k P) (D.nexp.hkF i j b k' P')

def OffRange : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → (∀ j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)) ∧
  ∀ s P, D.ntw.hEig i s 0 P = 1

def HkSS : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  V0 D.nexp i j b ≤ ⨆ ev, (Eigsp D.nexp i j b ev ⊓ V0 D.nexp i j b)

end GlobalTheory.SupLaw
end
end

