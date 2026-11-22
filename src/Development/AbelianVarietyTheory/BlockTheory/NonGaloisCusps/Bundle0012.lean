import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockHodgeTateJumps
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (σ : Representation LL G V)

def IsJumpMultiset (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD σ τ) ∧ ∀ a : ℤ, multV PD σ τ a = (J.count a : ℤ)

end Jumps

def blockJumps (t : ℕ) : Multiset ℤ := (Finset.Ico (0 : ℤ) (t : ℤ)).val

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  rw [blockJumps, Multiset.count_eq_of_nodup (Finset.Ico _ _).nodup]
  simp

example : blockJumps 3 = {0, 1, 2} := by decide

def SplitsAs {k Γ : Type} [Field k] [Group Γ] {n r t : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) k)
    (P : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → Γ → k) : Prop :=
  ∃ e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)), ∀ (g : Γ) (u : Fin n → k),
    e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ c g * (e u).2 c)

example {k : Type} [Field k] (r t : ℕ) :
    SplitsAs (twistM (1 : kˣ →* Matrix (Fin (r + t)) (Fin (r + t)) k) (MonoidHom.id kˣ))
      (twistM (1 : kˣ →* Matrix (Fin r) (Fin r) k) (MonoidHom.id kˣ)) (fun (_ : Fin t) g => (g : k)) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ (by simp), fun g u => ?_⟩
  have h : ∀ (m : ℕ) (v : Fin m → k),
      (twistM (1 : kˣ →* Matrix (Fin m) (Fin m) k) (MonoidHom.id kˣ) g).mulVec v = (g : k) • v := by
    intro m v
    change ((g : k) • (1 : Matrix (Fin m) (Fin m) k)).mulVec v = _
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h, h, map_smul]
  rfl

section HidaSetting

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def BlockSplit (π : N.X i) : Prop :=
  SplitsAs (mapM (toK N i) (rO N i r π)) (mapM (toK N i) (rhoO N i ρ π))
    (fun (c : Fin R.t) g => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i))

def HidaSetting (π : N.X i) : Prop :=
  GoodR N i r ∧ π ∈ N.Z i ∧
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
    BlockSplit N i r ρ π

variable {N} (L : LocTheory) (nbr : Br.NBr N)

def BlockJumpsAt (π : N.X i) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  ∃ J : Multiset ℤ,
    IsJumpMultiset (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ J ∧
    IsJumpMultiset (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (rTwO N i r π))) τ
      (J + blockJumps R.t)

theorem BlockJumpsAt.mult {π : N.X i} {w : HeightOneSpectrum (𝓞 H.E)} {hw : w ∈ placesOver H.E (N.l i)}
    {τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw} (h : BlockJumpsAt i r ρ L nbr π w hw τ) (a : ℤ) :
    multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (rTwO N i r π))) τ a =
      multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ a +
        if 0 ≤ a ∧ a < (R.t : ℤ) then 1 else 0 := by
  obtain ⟨J, h1, h2⟩ := h
  rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
  split_ifs <;> simp

end HidaSetting

def BlockJumps_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    HidaSetting D.nd i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw),
      BlockJumpsAt i r ρ D.loc D.nbr π w hw τ

def BlockJumpsF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BlockJumps_at (Fm.D x i)

def BlockJumpsClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => BlockJumpsF Fm

theorem closed_of_all (h : ∀ D : D7, BlockJumps_at D) (𝒞 : FamClass) : BlockJumpsClosed 𝒞 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ _ => h _⟩⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockJumpCount
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def IsJumpMultiset (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, multV PD ρ τ a = (J.count a : ℤ)

theorem IsJumpMultiset.unique {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {J J' : Multiset ℤ}
    (h : IsJumpMultiset PD ρ τ J) (h' : IsJumpMultiset PD ρ τ J') : J = J' := by
  ext a
  exact_mod_cast (h.2 a).symm.trans (h'.2 a)

end Local

def blockJumps (t : ℕ) : Multiset ℤ := (Multiset.range t).map (fun k : ℕ => (k : ℤ))

example : blockJumps 3 = {0, 1, 2} := by decide

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsBlockSum (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ (g : GE N) (u : Fin R.nV → KK N i),
      e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)

end Glob

def blockJumps_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    π ∈ D.nd.Z i → IsHeckeGalois D.nd i π (r π) → IsBlockSum D.nd i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw),
      ∃ J : Multiset ℤ,
        IsJumpMultiset (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ J ∧
        IsJumpMultiset (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r π))) τ
          (J + blockJumps D.R.t)

def blockJumpsF {eps : ℝ} (Fm : FamP eps) (_CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, blockJumps_at (Fm.D x i)

def blockJumpsClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm CH => blockJumpsF Fm CH)

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < t then 1 else 0 := by
  have hn : (blockJumps t).Nodup := (Multiset.nodup_range t).map Nat.cast_injective
  have hm : a ∈ blockJumps t ↔ 0 ≤ a ∧ a < t := by
    simp only [blockJumps, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨a.toNat, by omega, by omega⟩
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem hn (hm.2 h)
  · exact Multiset.count_eq_zero.2 (fun h' => h (hm.1 h'))

theorem blockJumps_at.mult {D : D7} (h : blockJumps_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Z i) (hr : IsHeckeGalois D.nd i π (r π)) (hs : IsBlockSum D.nd i r ρ π)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ) :
    multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r π))) τ a =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ a +
        (if 0 ≤ a ∧ a < D.R.t then 1 else 0) := by
  obtain ⟨J, h1, h2⟩ := h i r ρ π hπ hr hs w hw τ
  rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
  push_cast
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CharPolyRootsConstruction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

def IsStdElt (g₀ : GE N) : Prop :=
  (∃ w ∈ placesOver H.E (N.l i), g₀ ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  ∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g₀ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])

def StdEltExists : Prop := ∀ i : N.Loc, ∃ g₀ : GE N, IsStdElt N i g₀

def blockPoly (eB X0 : MatN N i) : (N.O i)[X] :=
  Matrix.det ((X : (N.O i)[X]) • eB.map (C (R := N.O i)) - X0.map (C (R := N.O i)) + 1 -
    eB.map (C (R := N.O i)))

def ChosenBefore (eB e1 X0 : N.X i → MatN N i) : Prop :=
  InR N i r eB ∧ InR N i r e1 ∧ InR N i r X0 ∧
  ∀ x, (blockPoly N i (eB x) (X0 x)).Monic ∧ (blockPoly N i (eB x) (X0 x)).natDegree = R.t ∧
    ((blockPoly N i (eB x) (X0 x)).map (toK N i)).Separable

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

def IsEnlargement : Prop :=
  N₁.l i₁ = N.l i ∧ Function.Injective φ ∧ φ.Finite ∧
  (∀ v (y : N.Om), σ y ∈ N₁.plOm.1 v ↔ y ∈ N.plOm.1 v) ∧
  Subalgebra.toSubmodule (N₁.T i₁) = Submodule.span (N₁.O i₁)
    ((fun (f : N.X i → N.O i) (x₁ : N₁.X i₁) => φ (f (β.symm x₁))) '' (N.T i : Set (N.X i → N.O i))) ∧
  (∀ x, β x ∈ N₁.Z i₁ ↔ x ∈ N.Z i) ∧ N₁.S i₁ = N.S i ∧ N₁.Q i₁ = N.Q i ∧
  ∀ c, 1 ≤ c → c ≤ R.t → ∀ g : GE N,
    ((N₁.chi i₁ c (AlgEquiv.autCongr σ g) : (N₁.O i₁)ˣ) : N₁.O i₁) =
      φ ((N.chi i c g : (N.O i)ˣ) : N.O i)

variable {N i N₁ i₁}

def enlRep {a : ℕ} (M : N.X i → (GE N →* GL (Fin a) (N.O i))) (x₁ : N₁.X i₁) :
    GE N₁ →* GL (Fin a) (N₁.O i₁) :=
  (mapRep φ (M (β.symm x₁))).comp (AlgEquiv.autCongr σ).symm.toMonoidHom

def enlMat (a : N.X i → MatN N i) (x₁ : N₁.X i₁) : MatN N₁ i₁ := (a (β.symm x₁)).map φ

def RootsIn (eB X0 : N.X i → MatN N i) : Prop :=
  ∀ x, ∃ al : Fin R.t → KK N₁ i₁,
    (blockPoly N i (eB x) (X0 x)).map ((toK N₁ i₁).comp φ) = ∏ c, (X - C (al c))

end Enlarge

def ConstructionsExist (N : NData R H what₂) : Prop :=
  ∀ (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (g₀ : GE N),
    HidaSetting N i r ρ → IsStdElt N i g₀ →
    ∃ eB e1 X0 : N.X i → N.X i → MatN N i,
      (∀ π ∈ N.Z i, ChosenBefore N i r (eB π) (e1 π) (X0 π)) ∧
      (∃ (N₁ : NData R H what₂) (i₁ : N₁.Loc) (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁)
          (β : N.X i ≃ N₁.X i₁), IsEnlargement N i N₁ i₁ σ φ β ∧
          ∀ π ∈ N.Z i, RootsIn φ (eB π) (X0 π)) ∧
      ∀ (N₁ : NData R H what₂) (i₁ : N₁.Loc) (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁)
        (β : N.X i ≃ N₁.X i₁), IsEnlargement N i N₁ i₁ σ φ β →
        ∀ π ∈ N.Z i, RootsIn φ (eB π) (X0 π) →
          ∃ S : IdempotentChoiceData N₁ i₁, S.eB = enlMat φ β (eB π) ∧ S.e1 = enlMat φ β (e1 π) ∧
            S.X0 = enlMat φ β (X0 π) ∧ S.g0 = AlgEquiv.autCongr σ g₀ ∧
            GoodCongruenceObjects N₁ (enlRep σ φ β r) (enlRep σ φ β ρ) (β π) S

def ConstructionsExist_at (D : D7) : Prop := ConstructionsExist D.nd

def ConstructionsExistF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConstructionsExist_at (Fm.D x i)

def ConstructionsExistClosed (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ConstructionsExistF Fm)

def ConstructionsExistAll : Prop :=
  ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂), ConstructionsExist N

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DefiniteFormInstances
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFormInstances

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

abbrev Vsp (D : D7) (j : ℕ) : @HSpace D.host.E _ _ D.host.cmStar :=
  letI := D.host.cmStar; D.sp.V j

def IsDefiniteForm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Prop :=
  ∀ τ : E →+* ℂ, (∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re) ∨ (∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0)

def Hyp (D : D7) (j : ℕ) : Prop :=
  letI := D.host.cmStar
  CMData D.host.F D.host.E ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  (∀ w : PlE D.host, ¬ IsSplitPl D.host w → w ∉ placesOver D.host.E 2) ∧
  Module.finrank D.host.E (Vsp D j).V = D.R.nV ∧
  IsDefiniteForm (Vsp D j) ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → Formalism.HermitianLatticesTheory.IsUnimodularAt (Vsp D j).hT w.asIdeal (Vsp D j).L0

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A)

def SphericalInert (j : ℕ) (π : B.AU j) : Prop := ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w

def IsBaseChange (j : ℕ) (π : B.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  Pa.Nodup ∧
  Formalism.MainNotions.N.rankIso N A Pa = R.nV ∧
  (∀ w : PlE H, IsSplitPl H w → Formalism.MainNotions.N.isoLoc N A Pa w = B.locAU j π w) ∧
  (∀ w : PlE H, ¬ IsSplitPl H w → A.unr (Formalism.MainNotions.N.isoLoc N A Pa w) ∧
    A.frobEig (Formalism.MainNotions.N.isoLoc N A Pa w) = Formalism.MainNotions.N.ubc R.nV (B.satAU j π w)) ∧
  ∀ τ : H.E →+* ℂ, Formalism.MainNotions.N.isoInf N A Pa τ = B.infW j (B.wtAU j π) τ

end Concl

def KappaDegreeStatement (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Hyp D j →
    ∀ π : D.nbc.AU j, SphericalInert D.nbc j π → ∃ Pa : List (Part D.naut.CG), IsBaseChange D.nbc j π Pa

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, KappaDegreeStatement (Fm.D x i)

def ClosedAbsoluteShare (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => KudlaFamilyStatement Fm

section Comparison₂

open Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

def IsInstOf (D : D7) (j : ℕ) (I : AutInst) (e : I.E ≃+* D.host.E) : Prop :=
  letI := D.host.cmStar
  (∀ x, e (star x) = D.host.conj (e x)) ∧
  ∃ σ : Fin I.n ≃ Fin (Vsp D j).rank, (∀ a b, e (I.J a b) = (Vsp D j).gram (σ a) (σ b)) ∧
    ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ a, e (x a) • (Vsp D j).frame (σ a)) ∈ (Vsp D j).L0

def LiesUnder {E' : Type} [Field E'] [NumberField E'] (I : AutInst) (e : I.E ≃+* E')
    (v : HeightOneSpectrum (𝓞 I.F)) (w : HeightOneSpectrum (𝓞 E')) : Prop :=
  ∀ (y : 𝓞 I.F) (z : 𝓞 E'), (z : E') = e (algebraMap I.F I.E (y : I.F)) → (y ∈ v.asIdeal ↔ z ∈ w.asIdeal)

def Kloc (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Set I.Gf :=
  {x | x ∈ I.Kset ∧ ∀ a : Af I.F, a v = 0 → ∀ s t, ((1 : I.E) ⊗ₜ[I.F] a) * (I.fmat x - 1) s t = 0}

variable {G X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def IsClosedInv (ρ : G → (X →L[ℂ] X)) (U : Submodule ℂ X) : Prop :=
  IsClosed (U : Set X) ∧ ∀ g, ∀ f ∈ U, ρ g f ∈ U

def IsIrredSub (ρ : G → (X →L[ℂ] X)) (U : Submodule ℂ X) : Prop :=
  IsClosedInv ρ U ∧ U ≠ ⊥ ∧ ∀ U' ≤ U, IsClosedInv ρ U' → U' = ⊥ ∨ U' = U

def IsIsoSub (ρ : G → (X →L[ℂ] X)) (U U' : Submodule ℂ X) : Prop :=
  ∃ T : U ≃L[ℂ] U', ∀ g (f f' : U), (f' : X) = ρ g f → ((T f' : U') : X) = ρ g ((T f : U') : X)

def SpectrumTieAt (D : D7) (j : ℕ) : Prop :=
  ∃ (I : AutInst) (e : I.E ≃+* D.host.E), IsInstOf D j I e ∧
    ∃ (μf : Measure I.Gf) (_ : μf.IsHaarMeasure) (_ : SigmaFinite μf) (fund : Set I.GA)
      (ρ : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)),
      I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund ρ ∧
      ∃ cls : {U : Submodule ℂ (I.L2 μf fund) // IsIrredSub ρ U} → D.nbc.AU j,
        Function.Surjective cls ∧ (∀ U U', cls U = cls U' ↔ IsIsoSub ρ U.1 U'.1) ∧
        ∀ U (w : PlE D.host) (v : HeightOneSpectrum (𝓞 I.F)), ¬ IsSplitPl D.host w → LiesUnder I e v w →
          (D.nbc.sphAU j (cls U) w ↔ ∃ f ∈ U.1, f ≠ 0 ∧ ∀ k ∈ Kloc I v, ρ (1, k) f = f)

def SpectrumTie : FamClass := fun Fm =>
  ∀ x : ℝ, Fm.x1 < x → ∀ (i : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x i).R.m → SpectrumTieAt (Fm.D x i) j

def ClosedFamilySpectrumCondition (𝒞 : FamClass) : Prop := ClosedAbsoluteShare fun Fm => 𝒞 Fm ∧ SpectrumTie Fm

end Comparison₂

theorem ClosedAbsoluteShare.tied {𝒞 : FamClass} (h : ClosedAbsoluteShare 𝒞) : ClosedFamilySpectrumCondition 𝒞 := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := h e he hle
  exact ⟨K, fun Fm CH hc hL => hK Fm CH hc.1 hL⟩

theorem isBaseChange_embAV {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (B : NBC A) (i : N.Loc) (P : A.AV i) (Pa : List (Part A.CG)) :
    IsBaseChange B (N.j i) (B.embAV i P) Pa ↔ Formalism.MainNotions.N.IsBCV N A i P Pa := by
  have hinj : Function.Injective fun p : Part A.CG => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d) := by
    rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ h
    simp only [Prod.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨⟨rfl, h1⟩, rfl⟩ := h
    rw [eq_of_heq h1]
  unfold IsBaseChange Formalism.MainNotions.N.IsBCV
  rw [List.nodup_map_iff hinj]
  simp only [B.embAV_loc, B.embAV_sat, B.embAV_inf i P]

example (α : ℂ) : Formalism.MainNotions.N.ubc 3 {α} = {α, α⁻¹, 1} := by
  have : Odd 3 := by decide
  simp [Formalism.MainNotions.N.ubc, this]

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFormInstances
end
end

