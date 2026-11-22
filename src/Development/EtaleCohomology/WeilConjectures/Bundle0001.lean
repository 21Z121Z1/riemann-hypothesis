import Development.EtaleCohomology.WeilConjectures.CurveCut
import Development.EtaleCohomology.WeilConjectures.GysinSeqCut

-- bundled from Development.EtaleCohomology.WeilConjectures.ContinCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.ContinCut

universe u v

def Chev : Prop := ∀ (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  ∀ N : ℕ, ∃ k, ∀ y ∈ K k, ∃ z : M, y = (l : ℤ_[l]) ^ N • z

def AbsCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (ρ : Representation ℤ_[l] G M)
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  (∀ (x : M) (k : ℕ), IsOpen {g : G | ρ g x - x ∈ K k}) →
  ∀ (φ : M →ₗ[ℤ_[l]] ℚ_[l]) (x : M), Continuous fun g => φ (ρ g x)

def Stab : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ (n : ℤ) (x : Hl l (sch.obj (geom (AlgebraicClosure K) p)) n 0)
    (k : ℕ), IsOpen {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
      (galHl l (AlgebraicClosure K) p n 0 σ x).1 k = x.1 k}

def FinGen : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ n : ℤ,
    Module.Finite ℤ_[l] (Hl l (sch.obj (geom (AlgebraicClosure K) p)) n 0)

def evk (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →ₗ[ℤ_[l]] HtL l k E n i :=
  (LinearMap.proj (R := ℤ_[l]) (φ := fun k => HtL l k E n i) k).comp (HlSub l E n i).subtype

theorem evk_apply (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) (x : Hl l E n i) : evk l E n i k x = x.1 k := rfl

theorem evk_anti (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : Antitone fun k => LinearMap.ker (evk l E n i k) := by
  intro a b hab x hx
  simp only [LinearMap.mem_ker, evk_apply] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact hx
  | succ d ih =>
    apply ih (Nat.le_add_right _ _)
    have h2 : red (l ^ (a + d + 1)) (l ^ (a + d)) E n i (x.1 (a + d + 1)) = x.1 (a + d) := x.2 (a + d)
    have h3 : (x.1 (a + d + 1) : Ht (l ^ (a + d + 1)) E n i) = 0 := hx
    rw [← h2, h3]; exact map_zero (red (l ^ (a + d + 1)) (l ^ (a + d)) E n i)

end LateralTheory.EWeil.ContinCut
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.LocalVanCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV
open LateralTheory.EWeil LateralTheory.EWeil.Gys

def LowVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), n < 2 * r →
  ∀ x : HZ (l ^ c) i P.j n, x = 0

def PointVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), 2 * r < n →
  ∀ (x : HZ (l ^ c) i P.j n) (t : P.X), ∃ (P' : SPair l r) (f : P'.Hom P),
    t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def Glue : Prop := ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ) (x : HZ (l ^ c) i P.j n),
  (∀ t : P.X, ∃ (P' : SPair l r) (f : P'.Hom P), t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0) →
  ∃ (P' : SPair l r) (f : P'.Hom P), Surjective f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def SPair.idHom {l r : ℕ} (P : SPair l r) : P.Hom P where
  fX := 𝟙 _
  fZ := 𝟙 _
  fU := 𝟙 _
  etale := inferInstance
  sqZ := IsPullback.of_horiz_isIso ⟨by simp⟩
  sqU := by simp

theorem goal_of (hL : LowVan) (hP : PointVan) (hG : Glue) : Gys.LocalVan := by
  intro hB l _ r P c i n hn x
  rcases lt_or_gt_of_ne hn with h | h
  · refine ⟨P, SPair.idHom P, show Surjective (𝟙 P.X) from inferInstance, ?_⟩
    rw [hL hB l r P c i n h x, map_zero]
  · exact hG l r P c i n x (fun t => hP hB l r P c i n h x t)

end LateralTheory.EWeil.Gys.LV
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.PurityCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et

namespace LateralTheory.EWeil.Gys.PurityCut
open LateralTheory.EWeil.Gys

abbrev pullE {l r : ℕ} {P' P : SPair l r} (f : P'.Hom P) (q : ℕ) (i n : ℤ) :
    HZ q i (initial.to P.Z) n →+ HZ q i (initial.to P'.Z) n :=
  pullZ q i (j := initial.to P.Z) (j' := initial.to P'.Z) f.fZ (𝟙 _) (initial.hom_ext _ _) n

def EmptyVan : Prop := ∀ (q : ℕ) (n i : ℤ), Subsingleton (Ht q (sch.obj (⊥_ Scheme.{0})) n i)

def LocB : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), n ≠ 0 →
  ∀ x : HZ (l ^ c) i (initial.to P.Z) n, ∃ (P' : SPair l r) (f : P'.Hom P), Function.Surjective f.fX ∧
    pullE f (l ^ c) i n x = 0

def Compare : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ),
  ∃ θ : ∀ (P : SPair l r) (c : ℕ) (i a b : ℤ), a + 2 * r = b →
      (HZ (l ^ c) i (initial.to P.Z) a ≃+ HZ (l ^ c) (i + r) P.j b),
    (∀ (P' P : SPair l r) (f : P'.Hom P) (c : ℕ) (i a b : ℤ) h x,
      θ P' c i a b h (pullE f (l ^ c) i a x) =
        pullZ _ _ f.fX f.fU f.sqU _ (θ P c i a b h x)) ∧
    ∀ (P : SPair l r) (c : ℕ) (i a b : ℤ) h x,
      θ P c i a b h (redZ (l ^ (c + 1)) (l ^ c) i (initial.to P.Z) a x) = redZ _ _ _ P.j _ (θ P (c + 1) i a b h x)

theorem goal_of (hS : SuppSeq) (hE : EmptyVan) (hC : Compare) : Purity := by
  intro hB l _ r
  obtain ⟨o, bd, hex, hnat, hred⟩ := hS
  obtain ⟨θ, hθn, hθr⟩ := hC hB l r
  have bij : ∀ (q : ℕ) (i : ℤ) (Z : Scheme.{0}) (n : ℤ), Function.Bijective (o q i (initial.to Z) n) := by
    intro q i Z n
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
      obtain ⟨z, rfl⟩ := ((hex q i (initial.to Z) m).2.2 x).1 hx
      have := hE q m i
      rw [Subsingleton.elim z 0, map_zero]
    · haveI := hE q n i
      exact ((hex q i (initial.to Z) n).1 y).1 (Subsingleton.elim _ _)
  let e : ∀ (q : ℕ) (i : ℤ) (Z : Scheme.{0}) (n : ℤ), HZ q i (initial.to Z) n ≃+ Ht q (sch.obj Z) n i :=
    fun q i Z n => AddEquiv.ofBijective (o q i (initial.to Z) n) (bij q i Z n)
  have he : ∀ q i Z n x, e q i Z n x = o q i (initial.to Z) n x := fun _ _ _ _ _ => rfl
  refine ⟨fun P c i a b h => (e (l ^ c) i P.Z a).symm.trans (θ P c i a b h), ?_, ?_⟩
  · intro P' P f c i a b h x
    simp only [AddEquiv.trans_apply]
    rw [← hθn]
    congr 1
    apply (e (l ^ c) i P'.Z a).injective
    rw [AddEquiv.apply_symm_apply, he, (hnat (l ^ c) i (initial.to P.Z) (initial.to P'.Z) f.fZ (𝟙 _)
      (initial.hom_ext _ _) a).1, ← he, AddEquiv.apply_symm_apply]
  · intro P c i a b h x
    simp only [AddEquiv.trans_apply]
    rw [← hθr]
    congr 1
    apply (e (l ^ c) i P.Z a).injective
    rw [AddEquiv.apply_symm_apply, he, (hred (l ^ (c + 1)) (l ^ c) i (initial.to P.Z) a).1, ← he,
      AddEquiv.apply_symm_apply]

end LateralTheory.EWeil.Gys.PurityCut
end
end

