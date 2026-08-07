import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360530975950334154, 360530979934016694⟩, ⟨1353205049082596561, 1353274843733385321⟩, true⟩

def state01 : KState := ⟨⟨360556517813457534, 360556521800341411⟩, ⟨691725937212540912, 691795814794172036⟩, true⟩

def words00 : List Nat := [360583227910961501, 360583226853276793, 360583227764173982, 360583228963198378, 360583228963513339, 360583228650154144, 360583226852598525, 360583225014159479, 360583223175763683, 360583221754598230]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564912029800003, 360564916019918706⟩, ⟨474228404608732087, 474298366020998061⟩, true⟩

def words01 : List Nat := [360583220724454899, 360583218956054016, 360583217187724760, 360583217776363007, 360583217974404183, 360583218172488441, 360583218172791141, 360583217464683184, 360583215273589569, 360583214567990504]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360512291276538913, 360512295269860202⟩, ⟨1838320953744468112, 1838390998183830818⟩, true⟩

def words02 : List Nat := [360583213862335262, 360583212704272662, 360583211140414976, 360583208824381810, 360583206508473239, 360583203191699083, 360583200854835447, 360583198736990538, 360583196619269160, 360583193495783220]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608529104151766, 360608533100679687⟩, ⟨(-657701620052569618), (-657631492449367982)⟩, true⟩

def words03 : List Nat := [360583190761947383, 360583189512180505, 360583188496107675, 360583188496447395, 360583187249309808, 360583184757033474, 360583182264884699, 360583180604756801, 360583181076717747, 360583182054364998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587446274667201, 360587450274437215⟩, ⟨(-110654708173672837), (-110584496454644499)⟩, true⟩

def words04 : List Nat := [360583182280874130, 360583183190273373, 360583185582119415, 360583187973880886, 360583189984393683, 360583190514622790, 360583190514929083, 360583190225598465, 360583189936230361, 360583188993698337]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360528357863475697, 360528361866448694⟩, ⟨1423242034189064434, 1423312329041366550⟩, true⟩

def words05 : List Nat := [360583190639957220, 360583192286154077, 360583192987616700, 360583193062139636, 360583193062424770, 360583192429257984, 360583192191862280, 360583192192202480, 360583191109479678, 360583188997767699]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570331269866587, 360570335276052719⟩, ⟨333207315410717868, 333277693692266384⟩, true⟩

def words06 : List Nat := [360583186886140717, 360583185190156198, 360583184238530466, 360583183245353750, 360583182252229937, 360583179967194636, 360583176204297182, 360583173128242850, 360583170052326213, 360583168456402826]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360553596775345579, 360553600784773791⟩, ⟨767840265186475845, 767910727680658613⟩, true⟩

def words07 : List Nat := [360583167962573195, 360583166342966509, 360583164723420168, 360583163846422143, 360583163846707587, 360583163579438292, 360583163312156929, 360583161906938960, 360583159686871836, 360583158549503609]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594987645934462, 360594991658568217⟩, ⟨(-307674327761496096), (-307603781970987002)⟩, true⟩

def words08 : List Nat := [360583157752883460, 360583157893827210, 360583157894133488, 360583157300820388, 360583156707491593, 360583155733957974, 360583156128960990, 360583156534716405, 360583156535019984, 360583156647142301]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360623682851490662, 360623686867346358⟩, ⟨(-1054016206764284263), (-1053945577219695421)⟩, true⟩

def words09 : List Nat := [360583156701087889, 360583156755128058, 360583156755406376, 360583156274861410, 360583154985632997, 360583152450214821, 360583149914926728, 360583148939210232, 360583150498637141, 360583152058022883]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259
