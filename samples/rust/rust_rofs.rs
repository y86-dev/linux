// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

use kernel::fs::{dentry, file, file::File, inode, inode::INode, sb::SuperBlock, Offset};
use kernel::prelude::*;
use kernel::{c_str, fs, time::UNIX_EPOCH, types::Either, types::Locked};

kernel::module_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

struct Entry {
    name: &'static [u8],
    ino: u64,
    etype: inode::Type,
}

const ENTRIES: [Entry; 3] = [
    Entry {
        name: b".",
        ino: 1,
        etype: inode::Type::Dir,
    },
    Entry {
        name: b"..",
        ino: 1,
        etype: inode::Type::Dir,
    },
    Entry {
        name: b"subdir",
        ino: 2,
        etype: inode::Type::Dir,
    },
];

const DIR_FOPS: file::Ops<RoFs> = file::Ops::new::<RoFs>();

struct RoFs;
impl fs::FileSystem for RoFs {
    const NAME: &'static CStr = c_str!("rust_rofs");

    fn fill_super(sb: &mut SuperBlock<Self>) -> Result {
        sb.set_magic(0x52555354);
        Ok(())
    }

    fn init_root(sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        let inode = match sb.get_or_create_inode(1)? {
            Either::Left(existing) => existing,
            Either::Right(mut new) => {
                new.set_fops(DIR_FOPS);
                new.init(inode::Params {
                    typ: inode::Type::Dir,
                    mode: 0o555,
                    size: ENTRIES.len().try_into()?,
                    blocks: 1,
                    nlink: 2,
                    uid: 0,
                    gid: 0,
                    atime: UNIX_EPOCH,
                    ctime: UNIX_EPOCH,
                    mtime: UNIX_EPOCH,
                })?
            }
        };
        dentry::Root::try_new(inode)
    }
}

#[vtable]
impl file::Operations for RoFs {
    type FileSystem = Self;

    fn seek(file: &File<Self>, offset: Offset, whence: file::Whence) -> Result<Offset> {
        file::generic_seek(file, offset, whence)
    }

    fn read_dir(
        _file: &File<Self>,
        inode: &Locked<&INode<Self>, inode::ReadSem>,
        emitter: &mut file::DirEmitter,
    ) -> Result {
        if inode.ino() != 1 {
            return Ok(());
        }

        let pos = emitter.pos();
        if pos >= ENTRIES.len().try_into()? {
            return Ok(());
        }

        for e in ENTRIES.iter().skip(pos.try_into()?) {
            if !emitter.emit(1, e.name, e.ino, e.etype.into()) {
                break;
            }
        }

        Ok(())
    }
}
