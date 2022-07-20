use crate::{assignments::*, lit::*, solver::*, solver_types::*, trail::*, watches::*};

use log::debug;
use std::ops::{Index, IndexMut};

//pub(crate) trait ClauseDB: Index<usize> + IndexMut<usize> {
