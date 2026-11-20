import Noctium.Frontend

open scoped Noctium

noctium_circuit cutoffInputs where
  public cutoff : UInt 64
end

noctium_contract NativeCheckpointPartial where
  cell firstMark : Native
  cell secondMark : Native
  entry apply uses cutoffInputs where
    write firstMark := 1
    checkpoint
    blockTimeBefore(cutoff) as beforeDeadline
    require beforeDeadline
    -- Make the continuation exceed the pinned Ledger 9 guaranteed budget.
    write secondMark := 1
    write secondMark := 2
    write secondMark := 3
    write secondMark := 4
    write secondMark := 5
    write secondMark := 6
    write secondMark := 7
    write secondMark := 8
    write secondMark := 9
    write secondMark := 10
    write secondMark := 11
    write secondMark := 12
    write secondMark := 13
    write secondMark := 14
    write secondMark := 15
    write secondMark := 16
    write secondMark := 17
    write secondMark := 18
    write secondMark := 19
    write secondMark := 20
    write secondMark := 21
    write secondMark := 22
    write secondMark := 23
    write secondMark := 24
    write secondMark := 25
    write secondMark := 26
    write secondMark := 27
    write secondMark := 28
    write secondMark := 29
    write secondMark := 30
    write secondMark := 31
    write secondMark := 32
    write secondMark := 33
    write secondMark := 34
    write secondMark := 35
    write secondMark := 36
    write secondMark := 37
    write secondMark := 38
    write secondMark := 39
    write secondMark := 40
    write secondMark := 41
    write secondMark := 42
    write secondMark := 43
    write secondMark := 44
    write secondMark := 45
    write secondMark := 46
    write secondMark := 47
    write secondMark := 48
    write secondMark := 49
    write secondMark := 50
    write secondMark := 51
    write secondMark := 52
    write secondMark := 53
    write secondMark := 54
    write secondMark := 55
    write secondMark := 56
    write secondMark := 57
    write secondMark := 58
    write secondMark := 59
    write secondMark := 60
    write secondMark := 61
    write secondMark := 62
    write secondMark := 63
    write secondMark := 64
    write secondMark := 65
    write secondMark := 66
    write secondMark := 67
    write secondMark := 68
    write secondMark := 69
    write secondMark := 70
    write secondMark := 71
    write secondMark := 72
    write secondMark := 73
    write secondMark := 74
    write secondMark := 75
    write secondMark := 76
    write secondMark := 77
    write secondMark := 78
    write secondMark := 79
    write secondMark := 80
    write secondMark := 81
    write secondMark := 82
    write secondMark := 83
    write secondMark := 84
    write secondMark := 85
    write secondMark := 86
    write secondMark := 87
    write secondMark := 88
    write secondMark := 89
    write secondMark := 90
    write secondMark := 91
    write secondMark := 92
    write secondMark := 93
    write secondMark := 94
    write secondMark := 95
    write secondMark := 96
    write secondMark := 97
    write secondMark := 98
    write secondMark := 99
    write secondMark := 100
    write secondMark := 101
    write secondMark := 102
    write secondMark := 103
    write secondMark := 104
    write secondMark := 105
    write secondMark := 106
    write secondMark := 107
    write secondMark := 108
    write secondMark := 109
    write secondMark := 110
    write secondMark := 111
    write secondMark := 112
    write secondMark := 113
    write secondMark := 114
    write secondMark := 115
    write secondMark := 116
    write secondMark := 117
    write secondMark := 118
    write secondMark := 119
    write secondMark := 120
    write secondMark := 121
    write secondMark := 122
    write secondMark := 123
    write secondMark := 124
    write secondMark := 125
    write secondMark := 126
    write secondMark := 127
    write secondMark := 128
  end
end
