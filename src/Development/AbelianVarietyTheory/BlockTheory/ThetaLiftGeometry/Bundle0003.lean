import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BlockSumMultiplicities
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockSumMultiplicities

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

variable (D : D7)

abbrev Fam (i : D.nd.Loc) (k : ℕ) : Type := D.nd.X i → (GE D.nd →* GL (Fin k) (D.nd.O i))

def BlockSum (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i) : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ (g : GE D.nd) (u : Fin D.R.nV → KK D.nd i),
      e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

def UnramIn (p : ℕ) : Prop :=
  ∀ v ∈ placesOver D.host.E p, Algebra.IsUnramifiedAt ℤ v.asIdeal

def OffTypes (p : ℕ) : Prop := ∀ k : Fin 2, p ≠ D.host.g k

def SizesLarge {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ (g : D.R.GG) (j : Fin D.R.m) (s : Bool), (etaHat L : ℤ) < szT (hcAt D g) j s

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

abbrev locRep {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Representation (Br.LL D.nbr i w hw) (Br.G D.nbr i w hw) (Fin k → Br.LL D.nbr i w hw) :=
  matRep (Br.loc D.nbr i w hw M)

def CrysAt {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M)

def mult {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) (a : ℤ) : ℤ :=
  multV (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M) τ a

def FinDR {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) : Prop :=
  FiniteDimensional (Br.LL D.nbr i w hw) ↥(DdRE (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M) τ)

def smallCount {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) (h : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc (-(h : ℤ)) (h : ℤ), mult D i w hw M τ a

def Over (τ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, ∃ y : D.what₂.LL,
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ (Br.cEw D.nbr i w hw x) ∧
      D.what₂.embLL y = D.host.emb g x

end Place

def jIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def HidaSetting (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i) : Prop :=
  GoodR D.nd i r ∧ π ∈ D.nd.Z i ∧ BlockSum D i r ρ π ∧ UnramIn D (D.nd.l i) ∧ OffTypes D (D.nd.l i)

variable {D}

def SecondTwistCrystallineSmall (L : SizeData₂ D) : Prop :=
  SizesLarge L →
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i), HidaSetting D i r ρ π →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ : Emb D i w hw, FinDR D i w hw (T2O D.nd i ρ π) τ ∧
      smallCount D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m

def SecondTwistCrystallineAtMost (L : SizeData₂ D) : Prop :=
  SizesLarge L →
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i), HidaSetting D i r ρ π →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ : Emb D i w hw, FinDR D i w hw (T2O D.nd i ρ π) τ ∧
      smallCount D i w hw (T2O D.nd i ρ π) τ (etaHat L) ≤ D.R.m

theorem SecondTwistCrystallineSmall.le {L : SizeData₂ D} (h : SecondTwistCrystallineSmall L) : SecondTwistCrystallineAtMost L :=
  fun hs i r ρ π hS w hw =>
    ⟨(h hs i r ρ π hS w hw).1, fun τ => ⟨((h hs i r ρ π hS w hw).2 τ).1, ((h hs i r ρ π hS w hw).2 τ).2.le⟩⟩

variable (D)

def SecondTwistJumps (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i), HidaSetting D i r ρ π →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) (g : D.R.GG), Over D i w hw τ g →
    ∀ a : ℤ, mult D i w hw (T2O D.nd i ρ π) τ a =
      ((jT2 (hcAt D g) (jIdx D i) (pos ε g)).count a : ℤ)

def PointsCrys : Prop :=
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV), GoodR D.nd i r → OffTypes D (D.nd.l i) →
  ∀ (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    CrysAt D i w hw (rO D.nd i r x)

def PointsJumps (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV), GoodR D.nd i r →
  ∀ (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) (g : D.R.GG), Over D i w hw τ g →
    ∀ a : ℤ, mult D i w hw (rTwO D.nd i r x) τ a =
      ((jR (hcAt D g) (jIdx D i) (pos ε g)).count a : ℤ)

def FromInputs : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (ε : ℤˣ), PointsCrys D → PointsJumps D ε → SecondTwistJumps D ε ∧ SecondTwistCrystallineSmall L

example {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) : (jT2 P j s).card = R.k - 1 + R.m := by
  cases s <;> simp [jT2, GlobalTheory.HTW.jW, cloud, lows]

end GlobalTheory.IndefiniteRowSideFullHecke.BlockSumMultiplicities
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits NumberField IsDedekindDomain GlobalTheory.HTW

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def Splits (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i]
      ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
        fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def Reads (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

def CrysAt {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M))

def mult {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ) : ℤ :=
  multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M)) τ a

def countIn {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (n : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc (-(n : ℤ)) n, mult D i w hw M τ a

def HasJumps {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (J : Multiset ℤ) : Prop :=
  ∀ a : ℤ, mult D i w hw M τ a = (J.count a : ℤ)

def CrysInput (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x, CrysAt D i w hw (rO D.nd i r x)

def JumpInput (ε : ℤˣ) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x τ g, Reads D i w hw τ g →
    HasJumps D i w hw (rTwO D.nd i r x) τ (jR (hcAt D g) (liftIdx D i) (pos ε g))

variable {D} (L : SizeData₂ D) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def ExactlyAt : Prop :=
  CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ, countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m

def AtMostAt : Prop :=
  CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ, countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) ≤ D.R.m

end Place

def HidaSetting (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  (∀ v ∈ placesOver D.host.E (D.nd.l i), eWL D.host.E v = 1) ∧
  (∀ k, D.nd.l i ≠ D.host.g k) ∧ GoodR D.nd i r ∧ π ∈ D.nd.Z i ∧ Splits D i r ρ π

variable {D}

def JumpsByLetter (L : SizeData₂ D) : Prop :=
  ∀ (ε : ℤˣ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    HidaSetting D i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrysInput D i w hw r → JumpInput D i w hw ε r →
      CrysAt D i w hw (T2O D.nd i ρ π) ∧
      ∀ τ g, Reads D i w hw τ g →
        HasJumps D i w hw (T2O D.nd i ρ π) τ (jT2 (hcAt D g) (liftIdx D i) (pos ε g)) ∧
        ((etaHat L : ℤ) < szT (hcAt D g) (liftIdx D i) (pos ε g) →
          countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m)

def SmallJumps (L : SizeData₂ D) : Prop :=
  ∀ C : ℝ, Roomy L C →
  ∀ (ε : ℤˣ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    HidaSetting D i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrysInput D i w hw r → JumpInput D i w hw ε r → ExactlyAt i w hw L ρ π

def SmallJumpsAll : Prop := ∀ (D : D7) (L : SizeData₂ D), SmallJumps L

theorem embLL_sigmaOf (g : D.R.GG) (x : D.host.E) :
    D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := by
  have := RingHom.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  simpa [Host.emb] using this

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineWindowLifts
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def UnramifiedInE (l : ℕ) : Prop :=
  ∀ v ∈ placesOver D.host.E l, v.asIdeal.ramificationIdx ℤ = 1

def InertInK (l : ℕ) : Prop := D.host.cls l = .signal ∨ D.host.cls l = .inertClass

def IsFrobAt (w : HeightOneSpectrum (𝓞 D.host.E)) (φ : D.R.GG) : Prop :=
  IsArithFrobAt ℤ (D.host.sigmaOf φ) w.asIdeal

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def Matches (θ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, θ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def CrystallineInput : Prop :=
  (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) ∧
    IsCrys (Br.PD D.loc D.nbr i w hw) (charRep (Br.locChi D.nbr i w hw (chiU D.nd i 1)))

def JumpInput (ε : ℤˣ) : Prop :=
  ∀ (θ : Emb D i w hw) (g : D.R.GG), Matches D i w hw θ g → ∀ (x : D.nd.X i) (a : ℤ),
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) θ a ↔
      a ∈ jR (hcAt D g) (liftIdx D i) (pos ε g)

def IsNumbering {n : ℕ} (θ : ZMod n → Emb D i w hw) : Prop :=
  n = Module.finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) ∧ Function.Bijective θ ∧
    ∀ (k : ZMod n) (c : Br.K0 D.nbr i w hw),
      θ (k + 1) (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).σ c)) =
        θ k (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) c)

end Place

def window {n : ℕ} (W : WordData n) (k : ZMod n) : Set ℤ :=
  (if W.up k then Set.Icc (W.sz k) (W.sz k + W.S) else Set.Icc (-(W.sz k + W.S)) (-W.sz k)) ∪
    Set.Icc (-(W.η : ℤ)) W.η

section Concl

variable (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def WordJumpsAt : Prop :=
  ∃ (φ τ : D.R.GG) (θ : ZMod (orderOf φ⁻¹) → Emb D i w hw),
    IsFrobAt D w φ ∧ IsNumbering D i w hw θ ∧
    (∀ k, Matches D i w hw (θ k) (letter τ φ⁻¹ k)) ∧
    (InertInK D (D.nd.l i) →
      Even (orderOf φ⁻¹) ∧ Alternates (pageWord L (liftIdx D i) ε τ φ⁻¹).up ∧
        ∀ k, (pageWord L (liftIdx D i) ε τ φ⁻¹).up k = false ↔ Even k.val) ∧
    ∀ T : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
      IsSubOfSums T.ρ (fun (x : D.nd.X i) (g : Br.G D.nbr i w hw) =>
        Br.loc D.nbr i w hw (rDuO D.nd i r x) g) →
      IsCrys (Br.PD D.loc D.nbr i w hw) T.ρ ∧
        ∀ k,
          JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (θ k) ((pageWord L (liftIdx D i) ε τ φ⁻¹).J1 k) ∧
          JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (θ k) (window (pageWord L (liftIdx D i) ε τ φ⁻¹) k) ∧
          JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (θ k)
            (Set.Icc (-((pageWord L (liftIdx D i) ε τ φ⁻¹).Mi k : ℤ))
              ((pageWord L (liftIdx D i) ε τ φ⁻¹).hi k : ℤ))

end Concl

def JumpsAlongWord : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    UnramifiedInE D (D.nd.l i) → (∀ k, D.nd.l i ≠ D.host.g k) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrystallineInput D i w hw r → JumpInput D i w hw r ε → WordJumpsAt D L ε i w hw r

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.UnramifiedLatticeEmbeddings
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

def window {n : ℕ} (W : WordData n) (a : ZMod n) : Set ℤ :=
  (if W.up a then Set.Icc (W.sz a) (W.sz a + W.S) else Set.Icc (-(W.sz a + W.S)) (-W.sz a)) ∪
    Set.Icc (-(W.η : ℤ)) W.η

def range {n : ℕ} (W : WordData n) (a : ZMod n) : Set ℤ :=
  Set.Icc (-(W.Mi a : ℤ)) (W.hi a : ℤ)

def UnramifiedIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ v ∈ placesOver E p, v.asIdeal.ramificationIdx ℤ = 1

def InertInK {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  H.cls p = .signal ∨ H.cls p = .inertClass

def IsFrobAt {R : Ranks} (H : Host R) (w : HeightOneSpectrum (𝓞 H.E)) (φ : R.GG) : Prop :=
  IsArithFrobAt ℤ (H.sigmaOf φ) w.asIdeal

section Place

variable (D : D7) (i : D.nd.Loc)

def liftIdx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def ChiConstituent (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∃ π ∈ D.nd.Z i, ∃ v : Fin D.R.nV → KK D.nd i, v ≠ 0 ∧
    ∀ g : GE D.nd, repK D.nd i r π g v = toK D.nd i ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

abbrev Lat : Type 1 :=
  LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)

def IsLetter (τ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

def IsNumbering {n : ℕ} (emb : ZMod n → Emb D i w hw) : Prop :=
  n = Module.finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) ∧ Function.Bijective emb ∧
    ∀ (a : ZMod n) (c : Br.K0 D.nbr i w hw),
      emb (a + 1) (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).σ c)) =
        emb a (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) c)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def CrysInput : Prop :=
  ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))

def JumpInput (ε : ℤˣ) : Prop :=
  ∀ (x : D.nd.X i) (τ : Emb D i w hw) (g : D.R.GG), IsLetter D i w hw τ g → ∀ u : ℤ,
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ u ↔
      u ∈ jR (hcAt D g) (liftIdx D i) (pos ε g)

def InTwistedDuals (T : Lat D i w hw) : Prop :=
  IsSubOfSums T.ρ fun (x : D.nd.X i) (g : Br.G D.nbr i w hw) => Br.loc D.nbr i w hw (rDuO D.nd i r x) g

def FitsWord {n : ℕ} (W : WordData n) (emb : ZMod n → Emb D i w hw) (T : Lat D i w hw) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) T.ρ ∧
    ∀ a : ZMod n,
      JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (emb a) (W.J1 a) ∧
      JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (emb a) (window W a) ∧
      JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (emb a) (range W a)

def WordAt (L : SizeData₂ D) (ε : ℤˣ) : Prop :=
  ∃ τ ψ : D.R.GG, IsFrobAt D.host w ψ⁻¹ ∧
    ∃ emb : ZMod (orderOf ψ) → Emb D i w hw,
      IsNumbering D i w hw emb ∧
      (∀ a, IsLetter D i w hw (emb a) (letter τ ψ a)) ∧
      (InertInK D.host (D.nd.l i) →
        Even (orderOf ψ) ∧ Alternates (pageWord L (liftIdx D i) ε τ ψ).up ∧
          ∀ a, (pageWord L (liftIdx D i) ε τ ψ).up a = false ↔ Even a.val) ∧
      ∀ T : Lat D i w hw, InTwistedDuals D i w hw r T →
        FitsWord D i w hw (pageWord L (liftIdx D i) ε τ ψ) emb T

end Place

def JumpsAlongWord : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    UnramifiedIn D.host.E (D.nd.l i) → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ChiConstituent D i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrysInput D i w hw r → JumpInput D i w hw r ε → WordAt D i w hw r L ε

def Inputs (D : D7) (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    (D.nd.Z i).Nonempty → ChiConstituent D i r ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
        JumpInput D i w hw r ε ∧
          (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → CrysInput D i w hw r)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs
end
end

