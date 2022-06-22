use super::*;

/// The termination status of an evaluation.
#[derive(Clone)]
pub enum TerminationStatus<'ctx> {
    /// Still running
    None,
    /// Returned
    Return(Vec<Values<'ctx>>),
    /// Aborted
    Abort(Values<'ctx>),
    /// Unfeasible execution path
    Unsat,
}

impl<'ctx> TerminationStatus<'ctx> {
    /// Return true iff the current evaluation state is final.
    pub fn is_final(&self) -> bool {
        match self {
            TerminationStatus::None => false,
            _ => true,
        }
    }
}

impl<'ctx> fmt::Display for TerminationStatus<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TerminationStatus::None => write!(f, "Still running"),
            TerminationStatus::Return(return_vals) => {
                writeln!(f, "Returns with values:")?;
                for (i, val) in return_vals.iter().enumerate() {
                    write!(f, "#{}: ", i)?;
                    // writeln!(f, "{}", val.iter().format(", "))?;
                    todo!()
                }
                Ok(())
            }
            TerminationStatus::Abort(val) => {
                // writeln!(f, "Aborts with error code {}.", val.iter().format(", "))
                todo!()
            }
            TerminationStatus::Unsat => writeln!(f, "Unsatisfied"),
        }
    }
}