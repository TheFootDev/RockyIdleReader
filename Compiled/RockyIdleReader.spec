# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['c:\\Users\\Foot\\Desktop\\Rocky Idle Reader\\RIR.py'],
    pathex=[],
    binaries=[],
    datas=[
        ('c:\\Users\\Foot\\Desktop\\Rocky Idle Reader\\GameData', 'GameData'),
        ('c:\\Users\\Foot\\Desktop\\Rocky Idle Reader\\item_price_array.json', '.'),
        ('c:\\Users\\Foot\\Desktop\\Rocky Idle Reader\\version.json', '.'),
    ],
    hiddenimports=['customtkinter', 'pygetwindow'],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='RockyIdleReader',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)
