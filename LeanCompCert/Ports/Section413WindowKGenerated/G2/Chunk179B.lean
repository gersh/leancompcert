import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179A

def state06 : KState := ⟨⟨360663670492656930, 360663672346791360⟩, ⟨(-1433045121089701773), (-1433022580537489781)⟩, true⟩

def words05 : List Nat := [360583885331923066, 360583885283363125, 360583886052486613, 360583886052714751, 360583885028117318, 360583881279714754, 360583877531686163, 360583878227514673, 360583882670578931, 360583887113199829]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579342663451803, 360579344519761005⟩, ⟨81703430087142362, 81726009709156930⟩, true⟩

def words06 : List Nat := [360583890003755893, 360583893012533934, 360583894947072323, 360583896881462574, 360583898023873203, 360583898307105869, 360583898307309202, 360583896844595388, 360583895382004475, 360583892433489951]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600780947685919, 360600782806144985⟩, ⟨(-303333787214003691), (-303311168948190155)⟩, true⟩

def words07 : List Nat := [360583895012282599, 360583897843873316, 360583899087742652, 360583901572353493, 360583903224404569, 360583904876336024, 360583909611017508, 360583912503187266, 360583913441673172, 360583914380087025]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360788850502138822, 360788852362756307⟩, ⟨(-3685976665830959155), (-3685954008746235233)⟩, true⟩

def words08 : List Nat := [360583918400560852, 360583924391807524, 360583930186945670, 360583935981479823, 360583938837859479, 360583941877090891, 360583947996248771, 360583954114792873, 360583963312557799, 360583974701217414]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360715317899898853, 360715319762693739⟩, ⟨(-2362669428894869844), (-2362646732627777372)⟩, true⟩

def words09 : List Nat := [360583984507587410, 360583994312891642, 360584005407068415, 360584018045832074, 360584029079918359, 360584040112817161, 360584048747657551, 360584054317908316, 360584061610618161, 360584068902595535]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179B
