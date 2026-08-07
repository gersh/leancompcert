import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571599998459027, 360571625114551805⟩, ⟨691549407547534276, 692613224590044056⟩, true⟩

def state01 : KState := ⟨⟨360583324558549790, 360583349682917796⟩, ⟨(-43652668130764630), (-42588332188477706)⟩, true⟩

def words00 : List Nat := [360582671480008414, 360582671480888783, 360582671363006883, 360582671118643487, 360582670874144267, 360582670565407035, 360582670527782125, 360582670603215231, 360582670603999486, 360582670562313939]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572120489910953, 360572145622602498⟩, ⟨658913568042336013, 659978425995068499⟩, true⟩

def words01 : List Nat := [360582670612726993, 360582670663405732, 360582670664132430, 360582670575613484, 360582670233561959, 360582669659029276, 360582669084346417, 360582668681185337, 360582668404659315, 360582668237812879]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568852779424701, 360568877920509066⟩, ⟨863769549846017691, 864834934236066387⟩, true⟩

def words02 : List Nat := [360582668070837904, 360582667729985706, 360582667349559698, 360582667223366030, 360582667096947456, 360582666826063817, 360582666373147393, 360582665698508748, 360582665023722965, 360582664544679895]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574379236875017, 360574404386248813⟩, ⟨517108894010014945, 518174798439017927⟩, true⟩

def words03 : List Nat := [360582664359743601, 360582664394748622, 360582664395538514, 360582664238225431, 360582664087599254, 360582663872901771, 360582663657953056, 360582663603394024, 360582663598879523, 360582663468149340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594889553437977, 360594914711138790⟩, ⟨(-769831075389401889), (-768764648483266097)⟩, true⟩

def words04 : List Nat := [360582663337236180, 360582663199874104, 360582663431193485, 360582663674271756, 360582663692623954, 360582663693504999, 360582663525606099, 360582663443875821, 360582663480767863, 360582663676916495]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360579328360031179, 360579353526115557⟩, ⟨206732133736882689, 207799086753765889⟩, true⟩

def words05 : List Nat := [360582663713924098, 360582663751023687, 360582664041651875, 360582664459158490, 360582664634420082, 360582664809802750, 360582664825748317, 360582664826629525, 360582664589448067, 360582664537695445]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594232562765949, 360594257737162850⟩, ⟨(-728677083534347037), (-727609608782046611)⟩, true⟩

def words06 : List Nat := [360582664686527071, 360582664895005129, 360582664975677717, 360582665056450630, 360582665072936896, 360582665281597500, 360582665609262582, 360582665937085023, 360582666058557759, 360582666244136102]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604419916611312, 360604445099325031⟩, ⟨(-1368193491287903942), (-1367125494448423318)⟩, true⟩

def words07 : List Nat := [360582666578960351, 360582666914032173, 360582667502346753, 360582667837906824, 360582667963784655, 360582668089734607, 360582668132219196, 360582668301406983, 360582668648994462, 360582668996770940]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570279983827868, 360570305174951037⟩, ⟨775107371568922432, 776175896393640564⟩, true⟩

def words08 : List Nat := [360582669167579086, 360582669168460574, 360582669086356855, 360582668997932928, 360582668909269915, 360582668703099931, 360582668244012220, 360582667657464857, 360582667070761840, 360582666632132016]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360537191934348495, 360537217133765954⟩, ⟨2852968293927862334, 2854037339593851146⟩, true⟩

def words09 : List Nat := [360582666492482483, 360582666549867062, 360582666550659786, 360582666481910667, 360582666160233751, 360582665722146402, 360582665283826790, 360582664839155290, 360582664310985479, 360582663588218086]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627
