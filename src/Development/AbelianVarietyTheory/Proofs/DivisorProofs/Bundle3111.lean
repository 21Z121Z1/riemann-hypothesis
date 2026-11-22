import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem locEq : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit

theorem pairValue : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N → IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 → ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := GlobalTheory.DiagPairing.exists_weilIs_diag_root

theorem geomLift : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := GlobalTheory.T.exists_geometric_symplectic_level_lift_siegel

theorem geomBij : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := GlobalTheory.T.basis_torsion_of_weilPairing_field

theorem buildCover : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := GlobalTheory.T.exists_siegelObject_deeper_level_of_sections

open GlobalTheory.LevCover in

theorem exists_levelCover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  intro h n N B B' _ _ ζ b j S s' c hn hN hnN hζ hc
  have hNpos : 0 < N := hN.pos
  have hnodd : Odd n := hN.of_dvd_nat hnN
  have hNn : N / n * n = N := Nat.div_mul_cancel hnN
  let b₀ : TBase B' n :=
    { ζ := b.ζ ^ (N / n)
      unit := by
        have := b.unit
        rw [← hNn, Nat.cast_mul] at this
        exact isUnit_of_mul_isUnit_right this
      prim := fun K _ β => by
        rw [Units.val_pow_eq_pow_val, map_pow]
        exact (b.prim K β).pow hNpos hNn.symm }
  have hb₀ : (b₀.ζ : B') = (b.ζ : B') ^ (N / n) := Units.val_pow_eq_pow_val _ _
  have hj : j ζ = (b₀.ζ : B') := hζ.trans hb₀.symm
  have RC := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B B' ζ (b₀.ζ : B') j S S (s' ≫ spMap j) s' (𝟙 S) hj
    (Category.id_comp _)
  obtain ⟨c₀, hpb⟩ := RC.1 c
  have hc₀ : c₀.Principal := RC.2.1 c c₀ hpb hc
  have hrel : ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')),
      SRel C' c₀ (N / n) 1 t ↔ SRel C' c (N / n) 1 t := fun T t C' => by
    have := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N B B' B' ζ (b₀.ζ : B') (b.ζ : B') S S T (s' ≫ spMap j) s' (t ≫ s') c c₀ C'
      (𝟙 S) t 1 1 (N / n) ((sRel_one_one_iff c₀ c (𝟙 S)).2 hpb)).1
    rwa [Category.comp_id] at this
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (fnOn s')
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, hadd, hpow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S c₀.A N (Fin h ⊕ Fin h → ℤ) c₀.ab hNS
  have R : RepTors c₀.A N _ Z et := ⟨hfin, het, hadd, hpow, huniv⟩
  haveI := hfin
  haveI := het
  have hNZ : IsUnit (N : Γ(Z.left, ⊤)) := by
    have := hNS.map Z.hom.appTop.hom
    rwa [map_natCast] at this
  have hlevN : ∀ a, c₀.lev a ^ N = 1 := fun a => by
    rw [← hNn, mul_comm, pow_mul, c₀.lev_tors, one_pow]
  obtain ⟨Ul, hUl, HUl⟩ := R.clopenCond (fun a => et a ^ (N / n)) (fun a => toUnit Z ≫ c₀.lev a)
    (fun a a' => by rw [hadd, mul_pow]) (fun a => by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow])
    (fun a a' => by rw [c₀.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hlevN, MonObj.comp_one])
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : c₀.diag.IsLB := pull_isLB c₀.isLB _
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a a' k _ _ g =>
    ∀ β : B' →+* k, g ≫ Z.hom ≫ s' = spMap β →
      Out.WeilIs c₀.A c₀.diag N ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a)
        ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a')
        (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a')))
  have hzN : ∀ (k : Type) [Field k] (β : B' →+* k), Units.map β.toMonoidHom b.ζ ^ N = 1 := fun k _ β =>
    Units.ext (by simpa using (b.prim k β).pow_eq_one)
  have locPair : ∀ a a', HkClopen.Loc (P2 a a') := fun a a' => by
    obtain ⟨v, hv, hW⟩ := pairValue h n B' _ S s' c₀ N Z (et a) (et a') hc₀.1 hNpos hNZ (hpow a) (hpow a')
    refine (locEq Z.left N v (Units.map (fnOn (Z.hom ≫ s')).toMonoidHom (b.ζ ^ (2 * omegaStd a a'))) hNZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      rw [map_fnOn _ g β hβ, ← unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hzN, one_zpow]
      exact unitOn_one'
    · have hW' := CommPairing.weilIs_pull hG c₀.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      have hu := map_fnOn _ g β hβ (b.ζ ^ (2 * omegaStd a a'))
      rw [show Units.map β.toMonoidHom (b.ζ ^ (2 * omegaStd a a')) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') from map_zpow _ _ _] at hu
      constructor
      · intro e β' hβ'
        obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans hβ)
        rw [← hu, ← e]
        exact hW'
      · intro H
        exact CommutatorPairing.weilIs_unique hG c₀.ab hLB hW' (hu ▸ H β hβ)

  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hNpos
  haveI := hκ
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + N • c₁) (a' + N • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β hβ
    have e1 : ∀ a c, et (a + N • c) = et a := fun a c => by rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
    rw [e1, e1]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + N • c₁) (a' + N • c₂) = omegaStd a a' + N * m :=
      ⟨_, omegaStd_add_nsmul N a a' c₁ c₂⟩
    have hz : Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd (a + N • c₁) (a' + N • c₂)) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (N * m) = N * (2 * m) by ring, zpow_mul _ (N : ℤ), zpow_natCast,
        hzN, one_zpow, _root_.mul_one]
    rw [hz]
    exact H β hβ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  obtain ⟨Wp, hWp, HWp⟩ := localization₂
  let U : Z.left.Opens := Ul ⊓ ⟨Wp, hWp.isOpen⟩
  have hU : IsClosed (U : Set Z.left) := hUl.inter hWp.isClosed
  obtain ⟨V, i, hV1, hV2, hi, Hi⟩ := exists_sub U hU
  have memWp : ∀ (Tw : Over S) (w : Tw ⟶ Z), (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Tw.left) (a a'),
      P2 a a' k (x ≫ w.left)) → Set.range w.left ⊆ Wp := by
    rintro Tw w H _ ⟨p, rfl⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point Tw.left p
    have h₁ := (HWp k (x ≫ w.left)).2 (H k x)
    have hp : x (default : PrimeSpectrum k) = p := by
      have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at this
    exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left p by rw [← hp]; rfl) ▸ h₁
  have hir : Set.range i.left ⊆ U := (Hi V i).2 ⟨𝟙 _, Category.id_comp _⟩
  have hiL := (HUl V i).2 fun _ hp => (hir hp).1
  have iW : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V.left) (a a'), P2 a a' k (x ≫ i.left) :=
    fun k _ _ x => (HWp k (x ≫ i.left)).1 (hir ⟨x (default : PrimeSpectrum k), rfl⟩).2

  have hprim : ∀ (k : Type) [Field k] (β : B' →+* k), IsPrimitiveRoot (Units.map β.toMonoidHom b.ζ) N :=
    fun k _ β => IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
  obtain ⟨C, φ, hsrel, hlev, huniv'⟩ := buildCover h n N (N / n) B' B' (b₀.ζ : B') (b.ζ : B') S V.left s'
    (V.hom ≫ s') V.hom c₀ (fun a => i ≫ et a) (fun a a' => by rw [hadd, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hpow, MonObj.comp_one])
    (fun a => by rw [← MonObj.comp_pow, hiL a, comp_toUnit_assoc]; rfl)
    (fun k _ _ x β z hx hz => by
      obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hz
      have hxS : (x ≫ V.hom) ≫ s' = spMap β := by rw [Category.assoc]; exact hx
      obtain ⟨e₀, a1, -, -, k1, o1, -⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k (x ≫ V.hom) β hn hN hnN hb₀
        hc₀ hxS
      have hpair : ∀ a a', Out.WeilIs c₀.A c₀.diag N
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a)
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a')
          (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := fun a a' =>
        weilIs_congr_base (by rw [Category.assoc, Over.w i]) (by simp) (by simp)
          (iW k x a a' β (by rw [← hx, Category.assoc, reassoc_of% (Over.w i)]))
      obtain ⟨b1, b2⟩ := geomBij h N k S (x ≫ V.hom) c₀.A c₀.diag (Units.map β.toMonoidHom b.ζ) e₀
        (fun a => (Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a) hLB hN (hprim k β) a1 k1 o1
        (fun a a' => by simp only [hadd, MonObj.comp_mul])
        (fun a => by rw [← MonObj.comp_pow, ← MonObj.comp_pow, hpow, MonObj.comp_one, MonObj.comp_one]) hpair
      exact ⟨b1, b2, hpair⟩)

  have h1T : ∀ (T : Scheme.{0}), (𝟙_ (Over T)).hom = 𝟙 T := fun T => rfl
  refine ⟨V.left, V.hom, C, hV1, hV2, ⟨fun pt => ?_⟩, (hrel V.left V.hom C).1 ⟨φ, hsrel⟩, fun T t C' hC' => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s')
    obtain ⟨e₀, a1, p1, l1, -, -, w1⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k x β hn hN hnN hb₀ hc₀ hβ
    obtain ⟨w, hw, -⟩ := huniv (Over.mk x) e₀ a1 p1
    have hx' : w.left ≫ Z.hom = x := Over.w w
    have hwl : Set.range w.left ⊆ Ul := (HUl (Over.mk x) w).1 fun a => by
      rw [MonObj.comp_pow, hw, l1, comp_toUnit_assoc]
    have hwW : w.left (default : PrimeSpectrum k) ∈ Wp := (HWp k w.left).2 fun a a' β' hβ' => by
      obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans (by rw [← Category.assoc, hx', hβ]))
      exact weilIs_congr_base hx'.symm (by rw [← hw a]; rfl) (by rw [← hw a']; rfl) (w1 a a')
    obtain ⟨w', hw'⟩ := (Hi _ w).1 fun _ hq => ⟨hwl hq, (HkClopen.range_subset_iff w.left Wp).2 hwW hq⟩
    obtain ⟨p, hp⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨w'.left p, by rw [← Scheme.Hom.comp_apply, Over.w w']; exact hp⟩
  · obtain ⟨φ', pb', hφ', low'⟩ := (hrel T t C').2 hC'
    let Tt : Over S := Over.mk ((𝟙_ (Over T)).hom ≫ t)
    let et' : (Fin h ⊕ Fin h → ℤ) → (Tt ⟶ c₀.A) := fun a => pushHom pb' (𝟙_ (Over T)) (C'.lev a)
    have a' : ∀ a a₂, et' (a + a₂) = et' a * et' a₂ := fun a a₂ => by simp only [et', C'.lev_add, map_mul]
    have p' : ∀ a, et' a ^ N = 1 := fun a => by simp only [et', ← map_pow, C'.lev_tors, map_one]
    obtain ⟨u, hu, -⟩ := huniv Tt et' a' p'
    have hul : ∀ a, (u ≫ et a).left = (C'.lev a).left ≫ φ' := fun a => by rw [hu]; rfl
    have hut : u.left ≫ Z.hom = t := (Over.w u).trans (Category.id_comp t)
    have hulow : Set.range u.left ⊆ Ul := (HUl Tt u).1 fun a => by
      rw [MonObj.comp_pow, hu, comp_toUnit_assoc]
      apply Over.OverMorphism.ext
      simp only [et', ← map_pow]
      show (C'.lev a ^ (N / n)).left ≫ φ' = (toUnit Tt).left ≫ (c₀.lev a).left
      rw [low' a, pow_one, Over.toUnit_left]
      exact (Category.id_comp t ▸ rfl : t ≫ (c₀.lev a).left = Tt.hom ≫ (c₀.lev a).left)
    have huW : Set.range u.left ⊆ Wp := memWp Tt u fun k _ _ x a a₂ β hβ =>
      weilTransport h N n B' B' (b₀.ζ : B') (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' pb' hφ' k x β
        (Units.map β.toMonoidHom b.ζ) ((x ≫ u.left) ≫ Z.hom) _ _ a a₂
        (by rw [← hβ, Category.assoc, reassoc_of% hut])
        rfl (by rw [Category.assoc, hut])
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
    obtain ⟨t₁, ht₁⟩ := (Hi Tt u).1 fun _ hq => ⟨hulow hq, huW hq⟩
    have ht₁π : t₁.left ≫ V.hom = t := (Over.w t₁).trans (Category.id_comp t)
    refine ⟨t₁.left, ⟨ht₁π, (huniv' T t₁.left B' (b.ζ : B') (t ≫ s') C').2 ⟨φ', by rw [ht₁π]; exact ⟨pb', hφ', low'⟩,
      fun a => (hul a).symm.trans (by rw [← ht₁]; simp)⟩⟩, ?_⟩
    rintro t₂ ⟨ht₂, hpb₂⟩
    obtain ⟨φ₂, hsr₂, hl₂⟩ := (huniv' T t₂ B' (b.ζ : B') (t ≫ s') C').1 hpb₂
    rw [ht₂] at hsr₂
    have e := GlobalTheory.T.principal_siegel_object_odd_level_rigid h n N (N / n) B' B' b₀ (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' φ₂ hn hnodd hc₀
      ⟨pb', hφ', low'⟩ hsr₂
    subst e
    let h₂ : Tt ⟶ V := Over.homMk t₂ (ht₂.trans (Category.id_comp t).symm)
    have : h₂ ≫ i = u := R.ext fun a => Over.OverMorphism.ext (by rw [hul, hl₂ a]; simp [h₂])
    exact congrArg (fun q => q.left) ((cancel_mono i).1 (this.trans ht₁.symm))

end GlobalTheory.SiegCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratedTwistSectionNonvanishingFiniteSetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  first | exact @GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | exact GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | (intros; apply GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingBoxProductOfRestrictedIsos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdBoxIso

section Ext

variable {B B₁ B₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂}

theorem gm_ext_g {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂') :
    gm ψ z ((extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂'))
        ((extLB M₁ M₂ b₁ b₂).g (extIdx a₁ a₂) (extIdx a₁' a₂')) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') := by
  have hm : ψ z ∈ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂') :=
    ⟨mem_extIdx h₁ h₂, mem_extIdx h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res ψ z _ hm _).trans ?_) ((gm_res ψ z _ hm _).trans ?_))
  · exact gm_pull_g M₁ b₁ ψ z (fun _ => a₁) (fun _ => a₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g M₂ b₂ ψ z (fun _ => a₂) (fun _ => a₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

theorem gm_ext_change {w : LB.Iso M (extLB M₁ M₂ b₁ b₂)} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z)
    (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (j j' : M.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂')
    (hj : ψ z ∈ M.U j) (hj' : ψ z ∈ M.U j') :
    gm ψ z _ (w.s (extIdx a₁ a₂, j)) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') * (gm ψ z _ (M.g j j'))⁻¹ *
        gm ψ z _ (w.s (extIdx a₁' a₂', j')) := by
  have hm : ψ z ∈ (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁ a₂, j) ⊓
      (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁' a₂', j') :=
    ⟨⟨mem_extIdx h₁ h₂, hj⟩, mem_extIdx h₁' h₂', hj'⟩
  have e := congrArg (gm ψ z _) (hw (extIdx a₁ a₂, j) (extIdx a₁' a₂', j'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M (extLB M₁ M₂ b₁ b₂) ψ z _ _ hm) (gm_res ψ z _ hm _))))
  rw [gm_ext_g ψ z a₁ a₁' a₂ a₂' h₁ h₁' h₂ h₂'] at e'
  exact e'

end Ext

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Sq

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂}

noncomputable def germ (p : T ⟶ B) (f : T ⟶ G) (h₁ : T ⟶ T₁) (h₂ : T ⟶ T₂) (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂))
    (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁))
    (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι)
    (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  (gm (r ≫ p) z _ (wM.s (extIdx a₁ a₂, jM)))⁻¹ * gw we₁ (r ≫ h₁) z a₁ (fun _ => n₁) *
    gw we₂ (r ≫ h₂) z a₂ (fun _ => n₂) * gm (r ≫ f) z _ (wL.s (extIdx n₁ n₂, jL))

variable {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem germ_change (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jM jM' : M.ι) (jL jL' : L.ι) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (n₁ n₁' : L₁.ι) (n₂ n₂' : L₂.ι)
    (cM : p (r z) ∈ M.U jM) (cM' : p (r z) ∈ M.U jM') (cL : f (r z) ∈ L.U jL) (cL' : f (r z) ∈ L.U jL')
    (c₁ : b₁ (p (r z)) ∈ M₁.U a₁) (c₁' : b₁ (p (r z)) ∈ M₁.U a₁')
    (c₂ : b₂ (p (r z)) ∈ M₂.U a₂) (c₂' : b₂ (p (r z)) ∈ M₂.U a₂')
    (d₁ : g₁ (f (r z)) ∈ L₁.U n₁) (d₁' : g₁ (f (r z)) ∈ L₁.U n₁')
    (d₂ : g₂ (f (r z)) ∈ L₂.U n₂) (d₂' : g₂ (f (r z)) ∈ L₂.U n₂') :
    germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ =
      gm (r ≫ p) z _ (M.g jM jM') * (gm (r ≫ f) z _ (L.g jL jL'))⁻¹ *
        germ p f h₁ h₂ wM wL we₁ we₂ r z jM' jL' a₁' a₂' n₁' n₂' := by
  have q₁ : p₁ (h₁ (r z)) = b₁ (p (r z)) := congrArg (fun g => g (r z)) eM₁.symm
  have q₂ : p₂ (h₂ (r z)) = b₂ (p (r z)) := congrArg (fun g => g (r z)) eM₂.symm
  have k₁ : f₁ (h₁ (r z)) = g₁ (f (r z)) := congrArg (fun g => g (r z)) eL₁.symm
  have k₂ : f₂ (h₂ (r z)) = g₂ (f (r z)) := congrArg (fun g => g (r z)) eL₂.symm
  have A := gm_ext_change hwM (r ≫ p) z a₁ a₁' a₂ a₂' jM jM' c₁ c₁' c₂ c₂' cM cM'
  have C := gm_ext_change hwL (r ≫ f) z n₁ n₁' n₂ n₂' jL jL' d₁ d₁' d₂ d₂' cL cL'
  have W₁ := hw₁ Z (r ≫ h₁) z a₁ a₁' (fun _ => n₁) (fun _ => n₁') (q₁ ▸ c₁) (q₁ ▸ c₁')
    (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁'))
  have W₂ := hw₂ Z (r ≫ h₂) z a₂ a₂' (fun _ => n₂) (fun _ => n₂') (q₂ ▸ c₂) (q₂ ▸ c₂')
    (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂'))
  rw [gm_pull_g L₁ f₁ (r ≫ h₁) z (fun _ => n₁) (fun _ => n₁') (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁')),
    Category.assoc, Category.assoc, ← eM₁, ← eL₁] at W₁
  rw [gm_pull_g L₂ f₂ (r ≫ h₂) z (fun _ => n₂) (fun _ => n₂') (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂')),
    Category.assoc, Category.assoc, ← eM₂, ← eL₂] at W₂
  rw [Category.assoc, Category.assoc] at A C
  unfold germ
  rw [A, C, W₁, W₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Sq

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Glue

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem exists_unit (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) (jM : M.ι) (jL : L.ι) :
    ∃ s : Γ(T, (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι),
        p (r z) ∈ M.U jM → f (r z) ∈ L.U jL → b₁ (p (r z)) ∈ M₁.U a₁ → b₂ (p (r z)) ∈ M₂.U a₂ →
        g₁ (f (r z)) ∈ L₁.U n₁ → g₂ (f (r z)) ∈ L₂.U n₂ →
        gm r z _ s = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ := by
  have q₁ : ∀ x, p₁ (h₁ x) = b₁ (p x) := fun x => congrArg (fun g => g x) eM₁.symm
  have q₂ : ∀ x, p₂ (h₂ x) = b₂ (p x) := fun x => congrArg (fun g => g x) eM₂.symm
  have k₁ : ∀ x, f₁ (h₁ x) = g₁ (f x) := fun x => congrArg (fun g => g x) eL₁.symm
  have k₂ : ∀ x, f₂ (h₂ x) = g₂ (f x) := fun x => congrArg (fun g => g x) eL₂.symm
  obtain ⟨W, hW⟩ : ∃ W : M₁.ι × M₂.ι × L₁.ι × L₂.ι → T.Opens, ∀ a x, x ∈ W a ↔
      (p x ∈ M.U jM ∧ f x ∈ L.U jL) ∧ (b₁ (p x) ∈ M₁.U a.1 ∧ b₂ (p x) ∈ M₂.U a.2.1) ∧
        (g₁ (f x) ∈ L₁.U a.2.2.1 ∧ g₂ (f x) ∈ L₂.U a.2.2.2) :=
    ⟨fun a => (p ⁻¹ᵁ M.U jM ⊓ f ⁻¹ᵁ L.U jL) ⊓ ((p ⁻¹ᵁ (b₁ ⁻¹ᵁ M₁.U a.1) ⊓ p ⁻¹ᵁ (b₂ ⁻¹ᵁ M₂.U a.2.1)) ⊓
      (f ⁻¹ᵁ (g₁ ⁻¹ᵁ L₁.U a.2.2.1) ⊓ f ⁻¹ᵁ (g₂ ⁻¹ᵁ L₂.U a.2.2.2))), fun _ _ => Iff.rfl⟩
  have l₀ : ∀ a, W a ≤ (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL) := fun a x hx =>
    ⟨mem_pull.2 ((hW a x).1 hx).1.1, mem_pull.2 ((hW a x).1 hx).1.2⟩
  have lM : ∀ a, W a ≤ p ⁻¹ᵁ ((LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a.1 a.2.1, jM)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.1.1 ((hW a x).1 hx).2.1.2, ((hW a x).1 hx).1.1⟩
  have lL : ∀ a, W a ≤ f ⁻¹ᵁ ((LB.div (extLB L₁ L₂ g₁ g₂) L).U (extIdx a.2.2.1 a.2.2.2, jL)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.2.1 ((hW a x).1 hx).2.2.2, ((hW a x).1 hx).1.2⟩
  have l₁ : ∀ a, W a ≤ h₁ ⁻¹ᵁ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => a.1, fun _ => a.2.2.1)) :=
    fun a x hx => ⟨mem_pull.2 ((q₁ x).symm ▸ ((hW a x).1 hx).2.1.1),
      mem_pull.2 ((k₁ x).symm ▸ ((hW a x).1 hx).2.2.1)⟩
  have l₂ : ∀ a, W a ≤ h₂ ⁻¹ᵁ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => a.2.1, fun _ => a.2.2.2)) :=
    fun a x hx => ⟨mem_pull.2 ((q₂ x).symm ▸ ((hW a x).1 hx).2.1.2),
      mem_pull.2 ((k₂ x).symm ▸ ((hW a x).1 hx).2.2.2)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(T, W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) a, r z ∈ W a →
      gm r z (W a) (u a) = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a.1 a.2.1 a.2.2.1 a.2.2.2 :=
    ⟨fun a => (res (lM a) (pullU p _ (wM.s (extIdx a.1 a.2.1, jM))))⁻¹ *
        res (l₁ a) (pullU h₁ _ (we₁.s (fun _ => a.1, fun _ => a.2.2.1))) *
        res (l₂ a) (pullU h₂ _ (we₂.s (fun _ => a.2.1, fun _ => a.2.2.2))) *
        res (lL a) (pullU f _ (wL.s (extIdx a.2.2.1 a.2.2.2, jL))),
      fun Z r z a hz => by
        simp only [map_mul, map_inv]
        rw [gm_res r z (lM a) hz, gm_pull r p z _ (lM a hz), gm_res r z (l₁ a) hz, gm_pull r h₁ z _ (l₁ a hz),
          gm_res r z (l₂ a) hz, gm_pull r h₂ z _ (l₂ a hz), gm_res r z (lL a) hz, gm_pull r f z _ (lL a hz)]
        rfl⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p x))
      obtain ⟨a₂, ha₂⟩ := exists_chart hM₂ (b₂ (p x))
      obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f x))
      obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, n₁, n₂),
        (hW _ x).2 ⟨⟨mem_pull.1 hx.1, mem_pull.1 hx.2⟩, ⟨ha₁, ha₂⟩, ⟨hn₁, hn₂⟩⟩⟩) u
    (fun a a' x hx => by
      have i := (hW a x).1 hx.1
      have i' := (hW a' x).1 hx.2
      have k := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ (𝟙 T) x jM jM jL jL a.1 a'.1 a.2.1 a'.2.1
        a.2.2.1 a'.2.2.1 a.2.2.2 a'.2.2.2 i.1.1 i.1.1 i.1.2 i.1.2 i.2.1.1 i'.2.1.1 i.2.1.2 i'.2.1.2
        i.2.2.1 i'.2.2.1 i.2.2.2 i'.2.2.2
      rw [gm_self hM (𝟙 T ≫ p) x i.1.1, gm_self hL (𝟙 T ≫ f) x i.1.2, inv_one, _root_.one_mul,
        _root_.one_mul] at k
      exact (hu _ (𝟙 T) x a hx.1).trans (k.trans (hu _ (𝟙 T) x a' hx.2).symm))
  refine ⟨s, fun Z r z a₁ a₂ n₁ n₂ cM cL c₁ c₂ d₁ d₂ => ?_⟩
  have hz := (hW (a₁, a₂, n₁, n₂) (r z)).2 ⟨⟨cM, cL⟩, ⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩
  exact (gm_res r z (l₀ _) hz s).symm.trans ((congrArg (gm r z (W _)) (hs _)).trans (hu Z r z _ hz))

end Glue

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

theorem exists_wiso : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → wM.IsGen → wL.IsGen → we₁.IsGen → we₂.IsGen → ∃ we : LB.Iso (L.pull f) (M.pull p), we.IsGen ∧ BoxSq wM wL we we₁ we₂ h₁ h₂ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  rw [isGen_iff] at hw₁ hw₂
  choose s hs using exists_unit (h₁ := h₁) (h₂ := h₂) hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  refine ⟨⟨fun q => s (q.1 PUnit.unit) (q.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z r z j j' k k' a₂ b₂' a₄ b₄
    obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p (r z)))
    obtain ⟨a₂', ha₂⟩ := exists_chart hM₂ (b₂ (p (r z)))
    obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f (r z)))
    obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f (r z)))
    have a₄' : f (r z) ∈ L.U (k PUnit.unit) := mem_pull.1 a₄
    have b₄' : f (r z) ∈ L.U (k' PUnit.unit) := mem_pull.1 b₄
    have c := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ r z j j' (k PUnit.unit) (k' PUnit.unit) a₁ a₁ a₂' a₂'
      n₁ n₁ n₂ n₂ a₂ b₂' a₄' b₄' ha₁ ha₁ ha₂ ha₂ hn₁ hn₁ hn₂ hn₂
    rw [← hs j _ Z r z a₁ a₂' n₁ n₂ a₂ a₄' ha₁ ha₂ hn₁ hn₂, ← hs j' _ Z r z a₁ a₂' n₁ n₂ b₂' b₄' ha₁ ha₂ hn₁ hn₂] at c
    rw [gm_pull_g L f r z k k' a₄ b₄]
    exact c
  · intro Z r z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
    have e := hs (J (r ≫ p)) (N (r ≫ f)) Z r z (J₁ ((r ≫ p) ≫ b₁)) (J₂ ((r ≫ p) ≫ b₂)) (N₁ ((r ≫ f) ≫ g₁))
      (N₂ ((r ≫ f) ≫ g₂)) (hJ _) (hN _) (hJ₁ _) (hJ₂ _) (hN₁ _) (hN₂ _)
    show om wM z J₁ J₂ J (r ≫ p) * gm r z _ (s (J (r ≫ p)) (N (r ≫ f))) = _
    rw [e]
    unfold germ om
    simp only [_root_.mul_assoc, mul_inv_cancel_left]

end GlobalTheory.ProdBoxIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMap
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_hodge_to_omega : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A),
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega, ∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c)) := by
  intro p _ R _ N hN A _ hA G t
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap R A p G t hA
  have hinj := GlobalTheory.PDivGroup.rigOfOmega_injective_of_pow p R N hN G
  have hmem : ∀ c : PrimitiveSubmodule A, (L ∘ₗ (PrimitiveSubmodule A).subtype) c ∈ LinearMap.range G.rigOfOmega := by
    intro c
    have hc : c.1.1 ∈ F1 (A.hom ≫ 𝟙 _) := c.2
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨β, hβ⟩ := hc
    have hβp : Form.cl _ β ∈ primDR A := hβ ▸ c.1.2
    obtain ⟨w, -, hw⟩ := GlobalTheory.PtExt.isCan_form R A p G t β hβp
    have hcc : (⟨_, hβp⟩ : primDR A) = c.1 := Subtype.ext hβ
    rw [hcc] at hw
    exact ⟨w, ((hL _ _).1 hw).symm⟩
  refine ⟨(LinearEquiv.ofInjective G.rigOfOmega hinj).symm ∘ₗ
    (L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem, fun c ↦ ?_⟩
  rw [hL]
  have := (LinearEquiv.ofInjective G.rigOfOmega hinj).apply_symm_apply
    ((L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem c)
  exact (congrArg Subtype.val this).symm
end

