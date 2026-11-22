import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct

def cc (l : ℕ) (a : ℤ) : ℚ := ((1 + (l : ℚ)) ^ a - 1) / (-(l : ℚ))

def eigMs (LL : Type) [Field LL] (l : ℕ) (U : Multiset ℤ) (w j j' : ℤ) : Multiset LL :=
  U.bind fun u => (Finset.Ico j j').val.map fun j'' => ((cc l (j'' - (u - w)) : ℚ) : LL)

def DiagWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] (f : M →ₗ[F] M) (S : Multiset F) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) F M) (e : Fin m → F),
    (∀ s, f (b s) = e s • b s) ∧ Finset.univ.val.map e = S

def EigWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] (f : M →ₗ[F] M) (S : Multiset F) : Prop :=
  ∃ _ : Module.Finite F M, f.charpoly = (S.map fun s => Polynomial.X - Polynomial.C s).prod

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def qΔ : LetA O n := W.π₀ + ((PD.p : ℕ) : LetA O n)

def mulD (a : LetA O n) : W.DD T →ₗ[O] W.DD T := Algebra.lsmul O O (W.DD T) a

def NΔl (i : ZMod n) : Submodule O (W.DD T) := W.NΔ T ⊓ (W.Nl T i).restrictScalars O

def qN (i : ZMod n) (j : ℤ) : Submodule O (W.DD T) :=
  ((NΔl W T i).map (mulD W T (qΔ W ^ j.toNat))).comap (mulD W T (qΔ W ^ (-j).toNat))

abbrev qQuot (i : ZMod n) (j j' : ℤ) : Type :=
  ↥(qN W T i j) ⧸ (qN W T i j').submoduleOf (qN W T i j)

def IsNab (g : W.Gam) (a : LetA O n) (i : ZMod n) (j : ℤ) (nb : ↥(qN W T i j) →ₗ[O] ↥(qN W T i j)) : Prop :=
  ∀ x : ↥(qN W T i j),
    (a * W.π₀) • ((nb x : ↥(qN W T i j)) : W.DD T) = W.γD T g (x : W.DD T) - a • (x : W.DD T)

def DiagQuot (g : W.Gam) (a : LetA O n) (i : ZMod n) (j j' : ℤ) (S : Multiset LL) : Prop :=
  qN W T i j' ≤ qN W T i j ∧
    Module.Free O (qQuot W T i j j') ∧ Module.Finite O (qQuot W T i j j') ∧
    Module.finrank O (qQuot W T i j j') = (j' - j).toNat * Module.finrank LL T.V ∧
    (∃ nb, IsNab W T g a i j nb) ∧
    ∀ nb, IsNab W T g a i j nb →
      ∃ hs : (qN W T i j').submoduleOf (qN W T i j) ≤ ((qN W T i j').submoduleOf (qN W T i j)).comap nb,
        DiagWith ((Submodule.mapQ _ _ nb hs).baseChange LL) S

def SenIs (k : Type) [Field k] [Algebra O k] (g : W.Gam) (a : LetA O n) (i : ZMod n) (S : Multiset k) :
    Prop :=
  (∃ nb, IsNab W T g a i 0 nb) ∧
    ∀ nb, IsNab W T g a i 0 nb →
      ∃ hs : (qN W T i 1).submoduleOf (qN W T i 0) ≤ ((qN W T i 1).submoduleOf (qN W T i 0)).comap nb,
        EigWith ((Submodule.mapQ _ _ nb hs).baseChange k) S

def IsGenWith (g : W.Gam) (i : ZMod n) (b : W.DD T) (a : LetA O n) : Prop :=
  b ∈ NΔl W T i ∧ (∀ x ∈ NΔl W T i, ∃ c ∈ W.AΔ, x = c • b) ∧ W.γD T g b = a • b

def SenPair (g : W.Gam) (a : LetA O n) (i : ZMod n) (U : Multiset ℤ) (w : ℤ) : Prop :=
  (∀ j j' : ℤ, j < j' → DiagQuot W T g a i j j' (eigMs LL PD.p U w j j')) ∧
    ∀ (k : Type) [Field k] [Algebra O k], Function.Surjective (algebraMap O k) →
      SenIs W T k g a i (U.map fun u => ((u - w : ℤ) : k))

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN_zero (i : ZMod n) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN W T i 0 = _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.NΔl W T i := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN, _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.mulD, Module.End.one_eq_id, Submodule.map_id,
    Submodule.comap_id]

theorem IsNab.unique {g : W.Gam} {a : LetA O n} {i : ZMod n} {j : ℤ}
    (h : Function.Injective fun x : W.DD T => (a * W.π₀) • x)
    {nb nb' : ↥(qN W T i j) →ₗ[O] ↥(qN W T i j)} (h₁ : IsNab W T g a i j nb) (h₂ : IsNab W T g a i j nb') :
    nb = nb' :=
  LinearMap.ext fun x => Subtype.ext (h ((h₁ x).trans (h₂ x).symm))

end Generic

example : cc 5 0 = 0 ∧ cc 5 1 = -1 ∧ cc 5 (-1) = 1 / 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [cc]

def SenWeightsAt (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  5 ≤ l → ∀ (K LL : FinExt l) (hA : CaseA K LL) (g : (H.W K 1 LL hA.2.2).Gam),
    (((H.W K 1 LL hA.2.2).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
    ∀ (h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ h i) →
      (∀ i, SenPair (H.W K 1 LL hA.2.2) T g 1 i (U i) 0) ∧
        ∀ (χ₁ : ↥(GK K) →* (↥(OL LL))ˣ) (w : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ)
          (hχ : IsCrysChar (LL := ↥LL.1) (P.PD K) (H.W K 1 LL hA.2.2).emb χ₁ w),
          (∀ i, 0 ≤ w i ∧ w i ≤ h i) →
          ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
            (b : (H.W K 1 LL hA.2.2).DD (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1))
            (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))),
            IsGenWith (H.W K 1 LL hA.2.2) (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) g i b a →
              SenPair (H.W K 1 LL hA.2.2) T g a i (U i) (w i)

def SenWeights : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (H : LocHW l P) (F : LocFon l P AI H), LocCmpT l P AI H F → SenWeightsAt l P H

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SenWeights
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SenWeightsAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct

def cA (F : Type) [Field F] [CharZero F] (l : ℕ) [Fact l.Prime] (a : ℤ) : F :=
  ((1 + (l : F)) ^ a - 1) / (-(l : F))

example (l : ℕ) [Fact l.Prime] : cA ℚ_[l] l 0 = 0 := by simp [cA]

example (l : ℕ) [Fact l.Prime] : cA ℚ_[l] l 1 = -1 := by
  have h : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  simp only [cA, zpow_one, add_sub_cancel_left]
  field_simp

def cMulti (F : Type) [Field F] [CharZero F] (l : ℕ) [Fact l.Prime] (U : Multiset ℤ) (j j' : ℤ) : Multiset F :=
  U.bind fun u => (Finset.Ico j j').val.map fun j'' => cA F l (j'' - u)

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

def mulBy (O : Type) [CommRing O] [Algebra O A] (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (a : A) : D →ₗ[O] D :=
  (a • (LinearMap.id : D →ₗ[A] D)).restrictScalars O

def qpow (q : A) (j : ℤ) (P : Submodule O D) : Submodule O D :=
  (P.map (mulBy O D (q ^ j.toNat))).comap (mulBy O D (q ^ (-j).toNat))

example (q : A) (P : Submodule O D) : qpow q 0 P = P := by
  ext x
  simp [qpow, mulBy]

example (q : A) (P : Submodule O D) (x : D) : x ∈ qpow q (-1) P ↔ q • x ∈ P := by
  simp [qpow, mulBy]

abbrev Quo (P Q : Submodule O D) : Type := ↥P ⧸ Q.submoduleOf P

def IsNab (π : A) (g : D →ₗ[O] D) (P Q : Submodule O D) (f : Module.End O (Quo P Q)) : Prop :=
  (∀ x : ↥P, ∃ y : ↥P, π • (y : D) = g x - x) ∧
    ∀ x y : ↥P, π • (y : D) = g x - x → f (Submodule.Quotient.mk x) = Submodule.Quotient.mk y

def DiagWith {F V : Type} [Field F] [AddCommGroup V] [Module F V] (f : Module.End F V) (S : Multiset F) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) F V) (e : Fin m → F),
    (∀ a, f (b a) = e a • b a) ∧ (Finset.univ : Finset (Fin m)).val.map e = S

def CharWith {k V : Type} [CommRing k] [AddCommGroup V] [Module k V] (f : Module.End k V) (S : Multiset k) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k V),
    (LinearMap.toMatrix b b f).charpoly = (S.map fun x => Polynomial.X - Polynomial.C x).prod

def Graded (F : Type) [Field F] [CharZero F] [Algebra O F] (l : ℕ) [Fact l.Prime] (π q : A) (g : D →ₗ[O] D)
    (P : Submodule O D) (d : ℕ) (U : Multiset ℤ) : Prop :=
  ∀ j j' : ℤ, j < j' →
    Nonempty (Module.Basis (Fin ((j' - j).toNat * d)) O (Quo (qpow q j P) (qpow q j' P))) ∧
      ∃ f : Module.End O (Quo (qpow q j P) (qpow q j' P)),
        IsNab π g (qpow q j P) (qpow q j' P) f ∧ DiagWith (f.baseChange F) (cMulti F l U j j')

def redSub (lam : O) (π : A) (P : Submodule O D) : Submodule O D :=
  P.map (lam • (LinearMap.id : D →ₗ[O] D)) ⊔ P.map (mulBy O D π)

def SenIs (lam : O) (π : A) (g : D →ₗ[O] D) (P : Submodule O D) (U : Multiset ℤ) : Prop :=
  ∃ f : Module.End O (Quo P (redSub lam π P)), IsNab π g P (redSub lam π P) f ∧
    CharWith (f.baseChange (O ⧸ Ideal.span {lam})) (U.map fun u => (u : O ⧸ Ideal.span {lam}))

end Operators

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def qq : LetA O n := W.π₀ + ((PD.p : ℕ) : LetA O n)

def Ni (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O (W.DD T) :=
  W.NΔ T ⊓ (W.Nl T i).restrictScalars O

def IsInvMult (g : W.Gam) (T₁ : LocLat G Qp LL O) (i : ZMod n) (e : W.DD T₁) (b : LetA O n) : Prop :=
  (∀ x, x ∈ Ni W T₁ i ↔ ∃ a ∈ W.AΔ, x = a • e) ∧ (∀ a ∈ W.AΔ, a • e = 0 → a i = 0) ∧
    b ∈ W.AΔ ∧ b • W.γD T₁ g e = e

def twγ (g : W.Gam) (T : LocLat G Qp LL O) (b : LetA O n) : W.DD T →ₗ[O] W.DD T :=
  mulBy O (W.DD T) b ∘ₗ W.γD T g

def Concl [CharZero LL] (l : ℕ) [Fact l.Prime] (lam : O) (T : LocLat G Qp LL O) (i : ZMod n)
    (g' : W.DD T →ₗ[O] W.DD T) (U : Multiset ℤ) : Prop :=
  Graded LL l W.π₀ (qq W) g' (Ni W T i) (Module.finrank LL T.V) U ∧ SenIs lam W.π₀ g' (Ni W T i) U

end Wach

def SenWeightsAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K LL : FinExt l) (hg : Good K 1 LL) (lam : ↥(OL LL)),
    Standing P K LL (H.W K 1 LL hg).emb lam →
    ∀ g : (H.W K 1 LL hg).Gam, (((H.W K 1 LL hg).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
    ∀ (h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ), (∀ i, 2 ≤ h i) →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      CrysWith (P.PD K) (H.W K 1 LL hg).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h i : ℤ)) →
      (∀ i, Concl (H.W K 1 LL hg) l lam T i ((H.W K 1 LL hg).γD T g) (U i)) ∧
      ∀ (χ₁ : ↥(GK K) →* (↥(OL LL))ˣ) (w : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ)
        (hχ : IsCrysChar (P.PD K) (H.W K 1 LL hg).emb χ₁ w), (∀ i, 1 ≤ w i ∧ w i ≤ (h i : ℤ) - 1) →
        ∀ i, (∃ e b, IsInvMult (H.W K 1 LL hg) g (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) i e b) ∧
          ∀ e b, IsInvMult (H.W K 1 LL hg) g (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) i e b →
            Concl (H.W K 1 LL hg) l lam T i (twγ (H.W K 1 LL hg) g T b) ((U i).map fun u => u - w i)

def SenWeights : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (H : LocHW l P) (F : LocFon l P AI H), LocCmpT l P AI H F → SenWeightsAt P H

end GlobalTheory.IndefiniteRowSideFullHecke.SenWeightsAlt
end
end

