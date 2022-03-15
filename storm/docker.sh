LOG_FILE="$PWD/storm-log"
WORK_DIR="$PWD/workdir"

touch "$LOG_FILE"
docker run -it \
  -v "$LOG_FILE":/logfile \
  -v "$WORK_DIR":/storm/temp \
  --cap-add=SYS_PTRACE --security-opt seccomp=unconfined \
  storm
