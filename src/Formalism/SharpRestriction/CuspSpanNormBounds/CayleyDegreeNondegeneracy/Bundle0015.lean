import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0014
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.AutomorphismsOfLiftTransitivity
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u : D.what₂.Word)

theorem automorphisms_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : CardAutEqCardIsometryStabilizer D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  have hD : ∀ φ : autLz D F0 Λ,
      ∃ γ : {γ : isom (D.sp.X 0).hT // gmap (extendByOne D γ.1) (latticeWithZ D F0 Λ) = latticeWithZ D F0 Λ},
        ActsAsExtendByOne D u F0 he φ.1 γ.1.1 := by
    rintro ⟨φ, σ, hσ, hσΛ, hφ⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨⟨⟨γ, hγ⟩, ?_⟩, actsAsExtendByOne_of_induced D u F0 he σ hσ γ hind φ hφ⟩
    rw [gmap_latticeWithZ_of_induced D u F0 σ hσ γ hind Λ, hσΛ]
  choose f hf using hD
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro φ₁ φ₂ h12
    apply Subtype.ext
    funext q
    obtain ⟨w, c, rfl⟩ := quotientClass_surjective D u hT F0 he hz q
    rw [hf φ₁ w c, hf φ₂ w c, h12]
  · rintro ⟨⟨γ, hγ⟩, hγΛ⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ hΛ
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγΛ)
    obtain ⟨n, hn, hnX, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow hΛ hLs
    have hσ : n * extendByIdentity D γ ∈ stabF D F0 := mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ)
    have hσΛ : gmap (n * extendByIdentity D γ) Λ = Λ := by rw [gmap_mul, hne]
    have hind : ∀ w, (n * extendByIdentity D γ) (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
      intro w
      change n (extendByIdentity D γ (D.sp.iXY 0 w)) - _ ∈ _
      have e : extendByIdentity D γ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ w) := by
        simpa using extendByIdentity_apply D γ w 0 (Submodule.zero_mem _)
      rw [e]
      refine hnX _ ((mem_perpS_iff_mem_orth D u F0 _).1 ?_)
      simpa using embedding_add_smul_z_mem_perp D u F0 he (γ w) 0
    let φ : WbQ D F0 → WbQ D F0 := Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
      (((n * extendByIdentity D γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrict
        (fun x hx => flag_stabilizer_mem_perp D u F0 _ hσ x hx))
      (fun x hx => flag_stabilizer_mem_isotropic D u F0 _ hσ x.1 hx)
    have hφ : ∀ (x : perpS (VS D) F0.X) (hx : (n * extendByIdentity D γ) x.1 ∈ perpS (VS D) F0.X),
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨(n * extendByIdentity D γ) x.1, hx⟩ := fun _ _ => rfl
    refine ⟨⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h1 := hf ⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩ w 0
    have h2 := actsAsExtendByOne_of_induced D u F0 he _ hσ γ hind φ hφ w 0
    exact quotientClass_injective_left D u hT F0 he hz (h1.symm.trans h2)

theorem gluing_mass_of_lift_transitivity (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingCount D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_iso_aut_count_genus D u hpos hlat (lattice_classes_of_lift_transitivity D u hL) (automorphisms_of_lift_transitivity D u hL) h4 h5

def GluingNumber : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ M ∈ genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    {𝓛 | (∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛) ∧ intersectFirstSummand D 𝓛 = M}.ncard = (Tu D u - 1) ^ D.R.f

theorem gluing_count_of_gluing_number (h : GluingNumber D u) : GluingCount D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ M hM
  have h1 := h hTp hT3 hsp F0 he hz Λ hΛ M hM
  refine ⟨Set.finite_of_ncard_ne_zero ?_, h1⟩
  have h2 : (Tu D u - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ (by omega)
  intro h0
  exact h2 (h1.symm.trans h0)

theorem gluing_mass_of_lift_and_number (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_lift_transitivity D u hpos hlat hL (gluing_count_of_gluing_number D u h4) h5

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTie
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_scanl_head (xs : List ℕ) (a : ℕ) : xs.scanl (· + ·) a = a :: (xs.scanl (· + ·) a).tail := by
  cases xs <;> simp [List.scanl_cons]

theorem rows_scanl_pw : ∀ (xs : List ℕ) (a : ℕ), (∀ x ∈ xs, 1 ≤ x) →
    ((xs.scanl (· + ·) a).tail).Pairwise (· < ·) ∧ ∀ y ∈ (xs.scanl (· + ·) a).tail, a < y := by
  intro xs
  induction xs with
  | nil => intro a _; simp [List.scanl]
  | cons x xs ih =>
    intro a h
    have hx : 1 ≤ x := h x (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih (a + x) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.scanl_cons, List.tail_cons]
    rw [rows_scanl_head xs (a + x)]
    refine ⟨List.pairwise_cons.2 ⟨fun y hy => ih2 y hy, ih1⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := ih2 y hy
      omega

theorem rows_pw_ext : ∀ (l₁ l₂ : List ℕ), l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ := by
  intro l₁ l₂ h1 h2 hm
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup (h1.imp ne_of_lt) (h2.imp ne_of_lt)).2 hm
  exact hp.eq_of_sortedLE (List.sortedLE_iff_pairwise.2 (h1.imp le_of_lt))
    (List.sortedLE_iff_pairwise.2 (h2.imp le_of_lt))

theorem rows_blockEnds_pw {i : ℕ} (p : Point ℂ i) :
    (ptBlockEnds p).Pairwise (· < ·) ∧ ∀ y ∈ ptBlockEnds p, 0 < y := by
  have h := rows_scanl_pw (p.1.map Prod.snd) 0 (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact (p.2.1 b hb).2)
  exact h

section Comparison₂

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def wordPairNormRelation (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    1 ≤ ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ∧
    ∀ l, l ≤ D.R.rS + 1 → leadMinorE (termGramMatrix X t) l ≠ 0 → 1 ≤ ∏ τ, absDl D (termGramMatrix X t) l τ ^ 2

theorem rows_Dmin_ne_iff (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) l ≠ 0 ↔ leadMinorE (termGramMatrix X t) l ≠ 0 := by
  rw [← norm_ne_zero_iff, d_norm_Dmin Y hrd t τ l hl]
  unfold absDl absReal
  have h0 : D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hrd _).ne'
  rw [mul_ne_zero_iff, norm_ne_zero_iff, map_ne_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, h0⟩⟩

theorem rows_TermPtsTie_of (hrd : 0 < D.host.rdE) (hN : wordPairNormRelation X u u') : TermPtsTie X Y := by
  intro t hG hrel
  have hR : ∀ τ, RelPt D (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) := fun τ => (Y.rel t hG hrel τ).1
  have mem_iff : ∀ τ l, l ∈ ptBlockEnds (Y.pt t τ) ↔ (1 ≤ l ∧ l ≤ D.R.rS + 1 ∧ leadMinorE (termGramMatrix X t) l ≠ 0) := by
    intro τ l
    constructor
    · intro h
      have hl := blockEnd_le (Y.pt t τ) l h
      exact ⟨(rows_blockEnds_pw (Y.pt t τ)).2 l h, hl, (rows_Dmin_ne_iff Y hrd t τ l hl).1 (cell_ne_of_mem D (hR τ) l h)⟩
    · rintro ⟨h1, hl, hne⟩
      exact cell_mem_blockEnds D (hR τ) l h1 hl ((rows_Dmin_ne_iff Y hrd t τ l hl).2 hne)
  refine ⟨fun τ => ?_, fun τ τ' => ?_, ?_, fun τ₀ l hl => ?_⟩
  · obtain ⟨_, _, hz, hz', hT, hT', _⟩ := Y.goodW τ
    exact ⟨hz, hz', hT, hT', hR τ⟩
  · exact rows_pw_ext _ _ (rows_blockEnds_pw _).1 (rows_blockEnds_pw _).1 fun x => by rw [mem_iff τ x, mem_iff τ' x]
  · rw [Finset.prod_congr rfl fun τ _ => d_Gf_eq Y hrd t τ]
    exact (hN t hG hrel).1
  · obtain ⟨_, h2, h3⟩ := (mem_iff τ₀ l).1 hl
    rw [Finset.prod_congr rfl fun τ _ => by rw [d_norm_Dmin Y hrd t τ l h2]]
    exact (hN t hG hrel).2 l h2 h3

end Comparison₂

end Formalism.MainNotions.BridgeLemma₂

end
end

