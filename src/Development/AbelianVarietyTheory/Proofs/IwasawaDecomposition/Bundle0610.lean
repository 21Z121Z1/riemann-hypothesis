import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointMemAbLocus
section
noncomputable section

namespace GlobalTheory.LocM.Cht.GoodOfZero

section Fibre

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isProper_thick {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) [Subsingleton D.X] :
    IsProper (pullback.snd G.hom (thick R I e)) := by
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hp := g.isKernel
  have : Mono g.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := GlobalTheory.UU.point_eq_of_subsingleton _ _
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono g.q.left := inferInstanceAs (Mono ((Over.forget _).map g.q))
  have : EffectiveEpi g.q.left := inferInstance
  have : IsIso g.q.left := isIso_of_mono_of_strongEpi _
  have := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  change IsProper (thickObj R I e G).hom
  rw [← Over.w g.q]
  infer_instance

theorem closedPoint_mem_abLocus {R : Type} [CommRing R] [IsLocalRing R] {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    (h : IsProper (pullback.snd G.hom (thick R (maximalIdeal R) e))) : closedPoint R ∈ abLocus G := by
  rintro K _ _ t ⟨q, hq⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective t
  have hk : ∀ a ∈ maximalIdeal R ^ (e + 1), φ.hom a = 0 := fun a ha => by
    have h1 : a ∈ maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero e) ha
    have h2 : Ideal.comap φ.hom q.asIdeal = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hq
    rw [← h2, show q.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ q.2] at h1
    exact h1
  let u : Sp K ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ φ.hom hk))
  have hu : u ≫ thick R (maximalIdeal R) e = Spec.map φ := by
    rw [← Spec.map_comp]; rfl
  have hp := (IsPullback.of_hasPullback (pullback.snd G.hom (thick R (maximalIdeal R) e)) u).paste_horiz
    (IsPullback.of_hasPullback G.hom (thick R (maximalIdeal R) e))
  rw [← hu, ← hp.isoPullback_inv_snd]
  infer_instance

end Fibre

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

theorem abOfTriv : GlobalTheory.LocM.Cht.AbOfTrivSt := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P A _ hs
  have hloc : IsLocalHom A.f := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((mem_maximalIdeal_ball (A.f a)).2 (A.f_loc a ((mem_maximalIdeal _).2 h))) ha⟩
  have e1 : spMap A.f (closedPoint _) = closedPoint A.R := comap_closedPoint A.f
  have e2 : P.yt (closedPoint ↥(intO ↥C.S)) = A.ι (closedPoint A.R) := by
    rw [← A.fac]
    exact congrArg A.ι e1
  rw [e2]
  exact (abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 _).2
    (closedPoint_mem_abLocus (isProper_thick (A.U.U.toUnifPre.gt 0)))

end GlobalTheory.LocM.Cht.GoodOfZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

section Lin

abbrev GVar (m a k b : ℕ) : Type :=
  {il : Fin m × Fin m // a ≤ (il.2 : ℕ) ∧ (il.2 : ℕ) < k ∧ k ≤ (il.1 : ℕ) ∧ (il.1 : ℕ) < b}

abbrev GPm (m a b : ℕ) : Type := {w : Equiv.Perm (Fin m) // ∀ i : Fin m, (i : ℕ) < a ∨ b ≤ (i : ℕ) → w i = i}

variable {S : Type} [CommRing S] {m a k b N : ℕ}

def gcell (x : GVar m a k b → S) (i l : Fin m) : S :=
  if h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b then x ⟨(i, l), h⟩ else if i = l then 1 else 0

def gvec {Q : Type} [AddCommGroup Q] [Module S Q] (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) : Fin m → Q :=
  fun l => ∑ i, gcell x i l • c (w.1 i)

theorem map_gcell {S' : Type} [CommRing S'] (φ : S →+* S') (x : GVar m a k b → S) (i l : Fin m) :
    φ (gcell x i l) = gcell (φ ∘ x) i l := by
  unfold gcell
  split_ifs <;> simp

theorem map_gvec {S' : Type} [CommRing S'] {φ : S →+* S'} {Q Q' : Type} [AddCommGroup Q] [Module S Q] [AddCommGroup Q']
    [Module S' Q'] (F : Q →ₛₗ[φ] Q') (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (l : Fin m) :
    F (gvec c w x l) = gvec (fun i => F (c i)) w (φ ∘ x) l := by
  simp only [gvec, map_sum, map_smulₛₗ, map_gcell]

theorem comp_gvec {S' : Type} [CommRing S'] (φ : S →+* S') {ι : Type} (c : Fin m → ι → S) (w : GPm m a b)
    (x : GVar m a k b → S) (l : Fin m) : φ ∘ gvec c w x l = gvec (fun i => φ ∘ c i) w (φ ∘ x) l := by
  funext r
  simp only [gvec, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_gcell]

variable (a b) in

def gxi (hk : k ≤ m) (c : Fin m → Fin (N + 1) → S) (w : GPm m a b) :
    Fin (plN N k + 1) → MvPolynomial (GVar m a k b) S :=
  plk (gvec (fun l => (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) ∘ c l) w
    (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S)) (Fin.castLE hk)

variable (a b) in

def gell (hk : k ≤ m) (D : Fin m → Fin (N + 1) → S) (w : GPm m a b) : Fin (plN N k + 1) → S :=
  lform D (w.1 ∘ Fin.castLE hk)

structure Cells {R : Type} [CommRing R] (ρ : R →+* S) {J : Type} (ξ : J → Fin (N + 1) → S) (ℓ : J → Fin (N + 1) → R) :
    Prop where
  one : ∀ j, ∑ q, ρ (ℓ j q) * ξ j q = 1
  gen : ∀ j, Function.Surjective (MvPolynomial.eval₂Hom ρ (ξ j))
  ovl : ∀ (K : Type) [Field K] (j j' : J) (ψ' : S →+* K), ∑ q, ψ' (ρ (ℓ j q)) * ψ' (ξ j' q) ≠ 0 →
    ∃ (ψ : S →+* K) (u : Kˣ), ψ.comp ρ = ψ'.comp ρ ∧ ψ' ∘ ξ j' = (u : K) • (ψ ∘ ξ j)
  lin : ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → J) (e : T → R),
    ∀ j', ξ j' q = ∑ t, ρ (e t) * ∑ q', ρ (ℓ (jj t) q') * ξ j' q'

example (R : Type) [CommRing R] : Cells (N := 0) (RingHom.id R) (fun _ : Unit => fun _ => 1) fun _ _ => 1 :=
  ⟨by simp, fun _ r => ⟨MvPolynomial.C r, by simp⟩, fun _ _ _ _ ψ _ => ⟨ψ, 1, rfl, by simp⟩,
    fun _ => ⟨Unit, inferInstance, id, fun _ => 1, by simp⟩⟩

end Lin

section Geom

variable {O : Type} [CommRing O] {Z Z' : Scheme.{0}}

def Lifts (s : Z ⟶ Sp O) {N : ℕ} (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (z : Sp R ⟶ Z) (y₀ : Sp R ⟶ PSpace O N) (y : Sp K ⟶ Z'), y₀ ≫ PSpace.str O N = z ≫ s →
    y ≫ f = spMap (algebraMap R K) ≫ z → y ≫ q = spMap (algebraMap R K) ≫ y₀ →
    ∃ z' : Sp R ⟶ Z', spMap (algebraMap R K) ≫ z' = y

structure CellCl (s : Z ⟶ Sp O) (ch : Charts Z) (g : ∀ a, O →+* ch.R a) {V J : Type} {N : ℕ}
    (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N)
    (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')) : Prop where
  proj : IsProjOver (f ≫ s)
  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z'
  flat : Flat (f ≫ s)
  ovr : q ≫ PSpace.str O N = f ≫ s
  opn : ∀ a j, IsOpenImmersion (κ a j)
  sq : ∀ a j, κ a j ≫ f = spMap (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) ≫ ch.χ a
  pl : ∀ a j, ∃ hv, κ a j ≫ q = pt ((MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)).comp (g a)) (ξ a j) hv
  cover : ⋃ a, ⋃ j, Set.range (κ a j) = f ⁻¹' ch.carrier
  dense : Dense (f ⁻¹' ch.carrier)
  inj : ∀ (K : Type) [Field K] (w w' : Sp K ⟶ Z'), Set.range (w ≫ f) ⊆ ch.carrier → w ≫ f = w' ≫ f → w ≫ q = w' ≫ q →
    w = w'
  lift : Lifts s f q

variable {C : Coc Z} {N k : ℕ} (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k))

def Car {K : Type} [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K) : Prop :=
  ∃ (g : O →+* K) (hv : _), w ≫ q = pt g (plk (fun l => ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (ξ l)) id) hv

def Planar : Prop :=
  ∀ x : Z', ∃ (U : Z'.Opens) (_ : IsAffineOpen U) (α : C.A) (a : GL (Fin (C.n α)) Γ(Z', U)), x ∈ U ∧ U ≤ f ⁻¹ᵁ C.B α ∧
    ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K),
      Car Em f q w α h ξ → ∀ (l : Fin k) (j : Fin (C.n α)), k ≤ (j : ℕ) → ∑ i, ev w U hw (a j i) * ξ l i = 0

end Geom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Crd

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}

structure LCrd (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) : Type 1 where
  C : Coc X
  N : ℕ
  Em : C.Emb N
  crd : ∀ (α : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X), ⊤ ≤ z ⁻¹ᵁ C.B α →
    (TanM (z ≫ π) M.t.G →ₗ[S] (Fin (C.n α) → S))
  tr : ∀ (α β : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β)
    (v : TanM (z ≫ π) M.t.G), (C.tr α β z hα hβ).mulVec (crd β S z hβ v) = crd α S z hα v
  bc : ∀ (α : C.A) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ X) (z' : Sp S' ⟶ X)
    (_ : spMap φ ≫ z = z') (h : ⊤ ≤ z ⁻¹ᵁ C.B α) (h' : ⊤ ≤ z' ⁻¹ᵁ C.B α) (e : spMap φ ≫ z ≫ π = z' ≫ π)
    (v : TanM (z ≫ π) M.t.G), crd α S' z' h' (tanPull φ e v) = φ ∘ crd α S z h v
  inj : ∀ (α : C.A) (K : Type) [Field K] (z : Sp K ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ C.B α),
    Set.range z ⊆ π ⁻¹' Set.range M.j → Function.Injective (crd α K z h)

variable {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

def LCrd.emb (D : LCrd M π) (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α)
    (v : TanM (z ≫ π) M.t.G) : Fin (D.N + 1) → S := ((D.Em.A α).map (ev z _ h)).mulVec (D.crd α S z h v)

def IsFrVec (D : LCrd M π) (A : Atlas M π ty) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A)
    (cv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a) : Prop :=
  ∀ (a : A.ch.ι) (S : Type) [CommRing S] (φ : A.ch.R a →+* S) (z : Sp S ⟶ X), spMap φ ≫ A.ch.χ a = z →
    ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (u : TVecs Dw M.t (z ≫ π)), up u = (A.fr a).bc φ →
      ∀ i, φ ∘ cv a i = D.emb (α a) z h (u σ i)

def GRel (D : LCrd M π) (A : Atlas M π ty) (σ : E →+* ℂ) {k : ℕ} (hk : k ≤ Dw.mult σ) {X' : Scheme.{0}} (f : X' ⟶ X)
    (q : X' ⟶ PSpace V (plN D.N k)) {ty' : (E →+* ℂ) → Finset ℕ} (A' : Atlas M (f ≫ π) ty') : Prop :=
  ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : TVecs Dw M.t ((w ≫ f) ≫ π)),
    A'.FlagAt w (up u) ↔ A.FlagAt (w ≫ f) (up u) ∧
      ∀ α h, Car D.Em f q w α h fun i => D.crd α K (w ≫ f) h (u σ (Fin.castLE hk i))

end Crd

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def IsLat (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π) : Prop :=
  ∀ α : D.C.A, ∃ (V : t.B.X.Opens) (m : Fin (D.C.n α) → Γ(t.L.N.toMod, V)), D.C.B α ≤ g ⁻¹ᵁ V ∧ VB.IsFrame m ∧
    ∀ (τ : (Y Z.i).X ⟶ (Y t.B.i).X) (mu : SABMap (Y Z.i).t (Y t.B.i).t τ), LocM.IsTrans t.B.i Z.i τ mu →
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Z.X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α), Set.range z ⊆ Z.opn →
        ∀ (v : TanM (z ≫ Z.π) (Y Z.i).t.G) (v' : Sp (DualNumber K) ⟶ t.B.t.G.left) (hv' : IsTanAtG t.B.t (z ≫ g) v')
          (h' : ⊤ ≤ (z ≫ g) ⁻¹ᵁ V), v' ≫ t.B.tMap.φ = (tv v).left ≫ mu.φ →
          ∀ l, D.crd α K z h v l = tanEv t.B.t hv' h' (t.L.N.incl.app V (m l))

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagNeZeroOfTriangularIndependent
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem tri_diag_ne_zero : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (ι : Type) (c c' : Let m → ι → K)
    (d : Let m → K), (∀ τ, LinearIndependent K fun j : Fin (m τ) => c' ⟨τ, j⟩) → Tri c c' d → ∀ z, d z ≠ 0 := by
  classical
  intro T m K _ ι c c' d hli htri z hz
  obtain ⟨τ, i⟩ := z
  set f : Fin (m τ) → ι → K := fun j => c ⟨τ, j⟩ with hf
  let w : Finset (ι → K) := (Finset.Iio i).image f
  have hsub : ∀ j : Fin (m τ), j ≤ i → c' ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := by
    have hspan : ∀ j : Fin (m τ), j ≤ i →
        Submodule.span K (f '' {j' | j' < j}) ≤ Submodule.span K (w : Set (ι → K)) := by
      intro j hj
      refine Submodule.span_mono ?_
      rintro _ ⟨j', hj', rfl⟩
      simp only [w, Finset.coe_image, Finset.coe_Iio]
      exact ⟨j', lt_of_lt_of_le hj' hj, rfl⟩
    intro j hj
    have ht := htri ⟨τ, j⟩
    rcases lt_or_eq_of_le hj with hlt | heq
    · have h1 : c' ⟨τ, j⟩ - d ⟨τ, j⟩ • c ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := hspan j hj ht
      have h2 : c ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := by
        refine Submodule.subset_span ?_
        simp only [w, Finset.coe_image, Finset.coe_Iio]
        exact ⟨j, hlt, rfl⟩
      have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (d ⟨τ, j⟩) h2)
      simpa using this
    · subst heq
      have h1 := hspan j le_rfl ht
      simpa [hz] using h1
  let v : (Finset.Iic i) → ι → K := fun j => c' ⟨τ, j.1⟩
  have hv : LinearIndependent K v := (hli τ).comp (fun j : Finset.Iic i => j.1) Subtype.val_injective
  have hle := linearIndependent_le_span_aux' v hv (w : Set (ι → K)) (by
    rintro _ ⟨j, rfl⟩
    exact hsub j.1 (Finset.mem_Iic.1 j.2))
  have hw : Fintype.card (w : Set (ι → K)) ≤ (i : ℕ) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact (Finset.card_image_le).trans (by simp)
  have hv' : Fintype.card (Finset.Iic i) = (i : ℕ) + 1 := by
    rw [Fintype.card_coe]; simp
  omega

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdUnitPowSubOneStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_unit_pow_sub_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E), M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  first | exact @GlobalTheory.UnipKill.unit_pow_congr_one | exact GlobalTheory.UnipKill.unit_pow_congr_one | (intros; apply GlobalTheory.UnipKill.unit_pow_congr_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRingsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_base_change_local_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), (∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i) → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Φ : FlagTor Z e U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) (ex : Ix Dw → ℤ) (f : Rul Xo c), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z φ y → ex none = 0 → f ∈ GlobalTheory.AllWt.secZ Xo c ex → (∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx ex) ((Φ.C k).val f) (Φ.C k).Ybd) → ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v := by
  first | exact @GlobalTheory.CuspFrom.evR_mem_maximalIdeal_of_vanishOn | exact GlobalTheory.CuspFrom.evR_mem_maximalIdeal_of_vanishOn | (intros; apply GlobalTheory.CuspFrom.evR_mem_maximalIdeal_of_vanishOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_generic_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (ex : Ix Dw → ℤ) (g : Rul Xo c) (σ : c.F →+* ℂ) (ψ : Γ(C.Y.X, U) →+* ℂ) (y : FrPt Xo c (CAt σ)) (a b : Γ(C.Y.X, U)), fr.Tri (fnOf U hg) C.f0 t → ex none = 0 → g ∈ GlobalTheory.AllWt.secZ Xo c ex → ψ.comp φ = σ → Matches fr ψ y → fnOf U hg a = C.val g * ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : C.Y.Fnˣ)⁻¹ : C.Y.Fnˣ) * fnOf U hg b → ψ a = toC (evR Xo c g y) * ψ b := by
  first | exact @GlobalTheory.ShFam.ChartValue.value_at_point | exact GlobalTheory.ShFam.ChartValue.value_at_point | (intros; apply GlobalTheory.ShFam.ChartValue.value_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlagStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_eigenframe_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (y : C.Y.X) (V : C.Y.X.Opens), y ∈ V → ∃ (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), U ≤ V ∧ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genStr Z = spMap φ ∧ fr.Tri (fnOf U (gen_mem hy)) C.f0 t ∧ ∀ y' ∈ U, ∀ τ i, (C.gr τ i).IsEqn y' (t τ i) := by
  first | exact @GlobalTheory.ShFam.Spread.exists_frame_nhds | exact GlobalTheory.ShFam.Spread.exists_frame_nhds | (intros; apply GlobalTheory.ShFam.Spread.exists_frame_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableTangentBasis
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagEmb
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagEmb.Stab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}}
  (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

set_option maxHeartbeats 800000 in

theorem basis_of_lieBasis {n : ℕ} (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) (hB : IsLieBasis v) :
    (∀ j, IsTanAtG t x0 ((v j).left ≫ pullback.fst t.G.hom x0)) ∧ ∀ w, IsTanAtG t x0 w →
      ∃! a : Fin n → S, IsCombAtG t x0 (fun j => (v j).left ≫ pullback.fst t.G.hom x0) a w := by
  classical
  have hp := isGrpPullback_pullback t.G x0
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun l => (tan _).1 (hB.1 _), fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
  refine ⟨c, ?_, fun a ha => ?_⟩
  · have := (comb _ _ _).1 hc
    rw [hup] at this
    exact this
  · exact hu a ((comb _ _ _).2 (by rw [hup]; exact ha))

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f = Formalism.L2.Pj.dualMap f := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, Formalism.L2.Pj.dualMap]

theorem spMap_dualMapR_id (R : Type) [CommRing R] :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R)) = 𝟙 _ := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]
  exact Spec.map_id _

theorem exists_stabBasis (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (x : X) :
    ∃ (U : X.affineOpens) (n : ℕ) (v : Fin n → Tn t Γ(X, U.1)), x ∈ U.1 ∧ StabBasis t U.2.fromSpec v := by
  have := t.semi.smooth
  obtain ⟨U, hU, hxU, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange X t.G x ⊤ trivial
  have key : ∀ (R' : Type) [CommRing R'] (φ : Γ(X, U) →+* R'),
      (∀ j, IsTanAtG t (spMap φ ≫ hU.fromSpec) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ v₀ j)) ∧
        ∀ w, IsTanAtG t (spMap φ ≫ hU.fromSpec) w → ∃! a : Fin n → R', IsCombAtG t (spMap φ ≫ hU.fromSpec)
          (fun j => spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ v₀ j) a w := fun R' _ φ => by
    obtain ⟨v', h1, h2⟩ := hv R' φ _ _ (isGrpPullback_pullback t.G (spMap φ ≫ hU.fromSpec))
    have h := basis_of_lieBasis t (spMap φ ≫ hU.fromSpec) v' h2
    have e : (fun j => (v' j).left ≫ pullback.fst t.G.hom (spMap φ ≫ hU.fromSpec)) =
        fun j => spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ v₀ j := funext h1
    refine ⟨fun j => h1 j ▸ h.1 j, fun w hw => e ▸ h.2 w hw⟩
  refine ⟨⟨U, hU⟩, n, v₀, hxU, fun j => ?_, fun R' _ φ w hw => ?_⟩
  · have h := (key _ (RingHom.id _)).1 j
    have e : spMap (RingHom.id Γ(X, U)) = 𝟙 _ := Spec.map_id _
    rw [spMap_dualMapR_id, e, Category.id_comp, Category.id_comp] at h
    exact h
  · have h := (key R' φ).2 w hw
    rw [dualMapR_eq] at h
    exact h

end GlobalTheory.FlagEmb.Stab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_atlas_refining_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (C : Coc X), ∃ A' : Atlas M π ty, (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), A'.FlagAt w u ↔ A.FlagAt w u) ∧ ∃ α : A'.ch.ι → C.A, ∀ a, ⊤ ≤ A'.ch.χ a ⁻¹ᵁ C.B (α a) := by
  first | exact @GlobalTheory.DRFlag.Atlas.exists_refine | exact GlobalTheory.DRFlag.Atlas.exists_refine | (intros; apply GlobalTheory.DRFlag.Atlas.exists_refine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.CountableCompletion

open Cardinal IsLocalRing

theorem mk_adicCompletion_le_continuum (R : Type) [CommRing R] [Countable R] (I : Ideal R) :
    #(AdicCompletion I R) ≤ 𝔠 := by
  have hinj : Function.Injective
      (fun x : AdicCompletion I R => (x.1 : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Submodule R R))) :=
    fun x y h => Subtype.ext h
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    (mk_le_of_surjective (Submodule.mkQ_surjective _)).trans mk_le_aleph0).trans ?_
  simp

noncomputable abbrev completionCDVR (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] : CDVR :=
  haveI : CharZero (AdicCompletion (maximalIdeal R) R) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R)
  { V := AdicCompletion (maximalIdeal R) R }

theorem exists_cdvr_mk_le_continuum :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R →
      ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧
        Cardinal.mk T.V ≤ Cardinal.continuum := by
  intro R _ _ _ _ hR
  exact ⟨completionCDVR R, algebraMap R (AdicCompletion (maximalIdeal R) R),
    GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance,
    mk_adicCompletion_le_continuum R (maximalIdeal R)⟩

end GlobalTheory.CountableCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegralStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_isIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E), ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  first | exact @GlobalTheory.exists_common_denominator | exact GlobalTheory.exists_common_denominator | (intros; apply GlobalTheory.exists_common_denominator <;> assumption)
end

